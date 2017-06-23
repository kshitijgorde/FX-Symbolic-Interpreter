:- dynamic
    callgraph_edge/2,             % callgraph_edge((SourceCName,SourceMName,SourceMSig),(DestCName,DestMName,DestMSig))
    node_visited/1,               % node_visited((ClassName,MethodName,MethodSig))
    recursive_method/1,           % recursive_method((CName,MName,MSig))
    sync_method/1,                % sync_method((CName,MName,MSig))
    know_if_callback/1,           % know_if_callback(CName)
    backtracked_offset/2,         % backtracked_offset(CName,MSig,OriginOffset,Offset)
    method_instr_graph/4,         % method_instr_graph(ClassName,MethodFullSignature,StartOffset,InstrGraph)
    method_instr_graphs_built/2,  % method_instr_graphs_built(ClassName,MethodFullSignature)
    collapsed_method_instr_graph/2,  % collapsed_method_instr_graph(ClassName,MethodFullSignature)
    method_exception_handler/6,   % method_exception_handler(ClassName,MethodFullSignature,InstrOffset,ExceptionType,OffsetStart,OffsetEnd)
    return_node/3,                % return_node(ClassName,MethodFullSignature,Offset)
    backtracks_to_instr/2,        % backtracks_to_instr(Offset1,Offset2)
    method_reaches_marked_code/1,    % method_reaches_marked_code(Class.MethodFullSignature)
    method_reaches_no_marked_code/1, % method_reaches_no_marked_code(Class.MethodFullSignature)
    edges_to_marked_nodes/2,      % edges_to_marked_nodes(InstrOffset,Destinations)
    safely_unmarked/1,            % safely_unmarked(InstrOffset)
    safely_marked/1.              % safely_marked(InstrOffset)

% build_callgraph(+StartInstrHandle,+ClassGen,+MethodGen)
%
% Explores a program starting with an initial instruction handle,
% class, and method, and produces a node list and call graph. The
% nodes are mapping rules with the concatenation of class and method names.
% The call graph is an asserted set of callgraph_edge rules in Prolog.
% Also asserts the method_instr_graphs, which links together a method's
% instruction_handles.
build_callgraph(StartInstrHandle,C,M) :-
    writeln('Building call graph...'),
    jpl_call(C,getClassName,[],CName),
    jpl_call(M,getName,[],MName),
    jpl_call(M,getSignature,[],MSig),
    retractall(node_visited(_)),
    assert(node_visited((CName,MName,MSig))),
    build_callgraph1(StartInstrHandle,C,M,[]),
    garbage_collect_atoms.

build_callgraph1(_,C,M,_) :-
    jpl_call(C,getClassName,[],CName),
    jpl_call(M,getName,[],MName),
    jpl_call(M,getSignature,[],MSig),
    atom_concat(MName,MSig,MethodFullSig),
    method_instr_graph(CName,MethodFullSig,_,_),!.
build_callgraph1(IH,C,M,InstrGraph) :-
    jpl_call(C,getClassName,[],CName),
    jpl_call(M,getName,[],MName),
    jpl_call(M,getSignature,[],MSig),
    atom_concat(MName,MSig,MethodFullSig),
    \+method_instr_graph(CName,MethodFullSig,_,_),
    jpl_call('mcparser.instr.InstructionInfo', getInstrType, [IH], InstrType),
    jpl_call(IH,getInstruction,[],Instr),
    jpl_call(Instr,getName,[],InstrName),
    jpl_call(IH,getNext,[],NextIH),
    jpl_call(IH,getPosition,[],Offset),
    (NextIH = @null ->
        NextOffset = @null
        ;
        jpl_call(NextIH,getPosition,[],NextOffset)),
    (InstrType = branch ->
        jpl_call('mcparser.instr.InstructionInfo',getBranchTarget,[IH],TargetIH),
        jpl_call(TargetIH,getPosition,[],TargetOffset),
        InstrGraph1 = [(Offset,TargetOffset)|InstrGraph],
        (jpl_call('mcparser.instr.InstructionInfo',isUnconditionalBranch,[IH],@true) ->
            NewInstrGraph = InstrGraph1
            ;
            ((InstrName == 'lookupswitch' ; InstrName == 'tableswitch') ->
                jpl_call('mcparser.instr.InstructionInfo',getSwitchTargets,[IH],SwitchTargetIHs),
                findall((Offset,SwitchTargetOffset),
                    (member(SwitchTargetIH,SwitchTargetIHs),
                     jpl_call(SwitchTargetIH,getPosition,[],SwitchTargetOffset)),
                    SwitchTargetPairs),
                append([(Offset,NextOffset)|SwitchTargetPairs],InstrGraph1,NewInstrGraph)
                ;
                NewInstrGraph = [(Offset,NextOffset)|InstrGraph1]))
        ;
        ((InstrType = return;InstrName == 'ret';InstrName == 'athrow') ->
            NewInstrGraph = InstrGraph
            ;
            ((InstrType = invoke,
              jpl_call('mcparser.instr.InstructionInfo',getInvokeDataLite,[C,M,IH],InvokeData),
              InvokeData \== @null,
              jpl_get(InvokeData,className,'java.lang.System'),
              jpl_get(InvokeData,methodName,'exit'))->
                NewInstrGraph = InstrGraph
                ;
                NewInstrGraph = [(Offset,NextOffset)|InstrGraph]))),
    (InstrType = invoke ->
        build_callgraph_invoke(IH,C,M),
        garbage_collect_atoms
        ;
        true),
    ((InstrType = return,\+return_node(CName,MethodFullSig,Offset)) ->
        assert(return_node(CName,MethodFullSig,Offset))
        ;
        true),
    !,
    (NextIH = @null ->
        jpl_call(M,getInstructionList,[],MIList),
        jpl_call(MIList,getStart,[],StartIH),
        format('asserting ret edges on ~w.~w~n',[CName,MethodFullSig]),
        add_ret_edges(NewInstrGraph,StartIH,FinalInstrGraph),
        format('asserting control flow graph for ~w.~w~n',[CName,MethodFullSig]),
        jpl_call(StartIH,getPosition,[],StartOffset),
        assert(method_instr_graph(CName,MethodFullSig,StartOffset,FinalInstrGraph)),
        assert_exception_handlers(CName,MethodFullSig,M)
        ;
        build_callgraph1(NextIH,C,M,NewInstrGraph)).
        
% build_callgraph_invoke(IH,C,M) :-
%    jpl_call('mcparser.instr.InstructionInfo', getInvokeDataLite, [C, M, IH], @null). % Doesn't return null...
build_callgraph_invoke(IH,C,M) :-
    jpl_call('mcparser.instr.InstructionInfo', getInvokeDataLite, [C, M, IH], InvokeData),
%    InvokeData \== @null,
    jpl_get(InvokeData, methodName, InvokeMethodName),
    jpl_get(InvokeData, className, InvokeClassName),
    jpl_get(InvokeData, signature, InvokeMSig),
    atom_concat(InvokeMethodName,InvokeMSig,InvokeMFullSig),
    method_instr_graphs_built(InvokeClassName,InvokeMFullSig). % Already been here; no need to reload all those classes
build_callgraph_invoke(IH,C,M) :-
    jpl_call('mcparser.instr.InstructionInfo', getInvokeDataLite, [C, M, IH], InvokeData),
%    InvokeData \== @null,
%    jpl_get(InvokeData, mgen, InvokeM),
%    jpl_get(InvokeData, cgen, InvokeC),
%    jpl_call(InvokeC, getClassName, [], InvokeClassName),
%    jpl_call(InvokeM, getName, [], InvokeMethodName),
%    jpl_call(InvokeM, getSignature, [], InvokeMSig),
%    atom_concat(InvokeMethodName,InvokeMSig,InvokeMFullSig),
    jpl_get(InvokeData, methodName, InvokeMethodName),
    jpl_get(InvokeData, className, InvokeClassName),
    jpl_get(InvokeData, signature, InvokeMSig),
    atom_concat(InvokeMethodName,InvokeMSig,InvokeMFullSig),
    \+method_instr_graphs_built(InvokeClassName,InvokeMFullSig),
    jpl_call(IH,getInstruction,[],Instr),
    jpl_call(Instr,getName,[],InstrName),
    % Obtain a list of all methods to which we could possibly travel (including overloaded versions)
    findall((ImplementorClassName,InvokeMethodName,InvokeMSig),
        (InstrName \== 'invokespecial',
         implemented_by(InvokeClassName,ImplementorClassName),
         jpl_call('mcparser.instr.InstructionInfo',getClassGen,[ImplementorClassName],ImplementorC),
         ImplementorC \== @null,
         jpl_call('mcparser.instr.InstructionInfo',getMethodFromClass,[ImplementorC,InvokeMFullSig],ImplementorM),
         ImplementorM \== @null,
         jpl_call(ImplementorC,getClassName,[],ImplementorCName),
         assert(method_instr_graphs_built(ImplementorCName,InvokeMFullSig))),
        ImplementorMethodList),
    jpl_call('mcparser.instr.InstructionInfo',getClassGen,[InvokeClassName],InvokeC),
    ((InvokeC \== @null,
      jpl_call('mcparser.instr.InstructionInfo',getMethodFromClass,[InvokeC,InvokeMFullSig],InvokeM),
      InvokeM \== @null) ->
        DestinationMethods = [(InvokeClassName,InvokeMethodName,InvokeMSig)|ImplementorMethodList]
        ;
        DestinationMethods = ImplementorMethodList),
    assert(method_instr_graphs_built(InvokeClassName,InvokeMFullSig)),
    % Now travel to each one, adding every corresponding edge and node
    build_callgraph_invoke1(C,M,DestinationMethods).
    
build_callgraph_invoke1(_,_,[]) :- garbage_collect_atoms.
build_callgraph_invoke1(C,M,[(DestCName,_DestMName,_DestMSig)|Dests]) :-
    trusted_class(DestCName),
    build_callgraph_invoke1(C,M,Dests).
build_callgraph_invoke1(C,M,[(DestCName,DestMName,DestMSig)|Dests]) :-
    \+trusted_class(DestCName),
    jpl_call(C,getClassName,[],CName),
    jpl_call(M,getName,[],MName),
    jpl_call(M,getSignature,[],MSig),
    (\+callgraph_edge((CName,MName,MSig),(DestCName,DestMName,DestMSig)) ->
        assert(callgraph_edge((CName,MName,MSig),(DestCName,DestMName,DestMSig))) ; true),
    (\+node_visited((DestCName,DestMName,DestMSig)) ->
        assert(node_visited((DestCName,DestMName,DestMSig))),
        jpl_call('mcparser.instr.InstructionInfo',getClassGen,[DestCName],DestC),
        atom_concat(DestMName,DestMSig,DestMFullSig),
        jpl_call('mcparser.instr.InstructionInfo',getMethodFromClass,[DestC,DestMFullSig],DestM),
        jpl_call(DestM, getInstructionList, [], DestIList),
        (DestIList \== @null ->
            jpl_call(DestIList, getStart, [], DestStart),
%            format('Method ~w.~w~w entered from ~w.~w~w~n',[DestCName,DestMName,DestMSig,CName,MName,MSig]),
            build_callgraph1(DestStart,DestC,DestM,[])
            ;
            true)
        ;
        true),
    build_callgraph_invoke1(C,M,Dests).

% build_callgraph_invoke1(C,M,NewC,NewM,NodeAssoc,FinalNodeAssoc,CallGraph,FinalCallGraph) :-
%    jpl_call(NewC, getClassName, [], NewClassName),
%    jpl_call(NewM, getName, [], NewMethodName),
%    jpl_call(NewM, getSignature, [], NewMSig),
%    jpl_call(NewM,hashCode,[],NewMHash),
%    jpl_call(M,hashCode,[],MHash),
%    jpl_call(C,getClassName,[],ClassName),
%    jpl_call(M,getName,[],MethodName),
%    jpl_call(M,getSignature,[],MSig),
% %    atom_concat(NewMethodName,NewMSig,NewFullMethodSig),
% %   % ensure edges get drawn to all implementors/inheritors of this class
% %   findall((NodeAssoc2,CallGraph2),
% %           (implemented_by(NewClassName,ImplementorClassName),
% %            jpl_call('mcparser.instr.InstructionInfo',getClassGen,[ImplementorClassName],ImplementorClassGen),
% %            jpl_call('mcparser.instr.InstructionInfo',getMethodFromClass,[ImplementorClassGen,NewFullMethodSig],ImplementorMethodGen),
% %            ImplementorMethodGen \== @null,
% %            jpl_call(ImplementorMethodGen,hashCode,[],ImplementorMethodGenHash),
% %            jpl_call(ImplementorClassGen,getClassName,[],ImplementorClassName),
% %            jpl_call(ImplementorMethodGen,getName,[],ImplementorMethodName),
% %            jpl_call(ImplementorMethodGen,getSignature,[],ImplementorMethodSig),
% %            union(CallGraph,[edge((MHash,ClassName,MethodName,MSig),
% %                                  (ImplementorMethodGenHash,ImplementorClassName,ImplementorMethodName,ImplementorMethodSig))],
% %                     CallGraph1),
% %            (\+get_assoc((ImplementorMethodGenHash,ImplementorClassName,ImplementorMethodName,ImplementorMethodSig),NodeAssoc,_) ->
% %                   put_method_assoc((ImplementorMethodGenHash,ImplementorClassName,ImplementorMethodName,ImplementorMethodSig),
% %                       NodeAssoc,white,NodeAssoc1),
% %                   build_callgraph_invoke1(C,M,ImplementorClassGen,ImplementorMethodGen,NodeAssoc1,NodeAssoc2,CallGraph1,CallGraph2)
% %                   ;
% %                   NodeAssoc1 = NodeAssoc,
% %                   CallGraph2 = CallGraph1)),
% %           NodeAssocCallGraph1),
% %   findall(NodeAssoc1,member((NodeAssoc1,_),NodeAssocCallGraph1),NodeAssoc1List),
% %   findall(CallGraph1,member((_,CallGraph1),NodeAssocCallGraph1),CallGraph1List),
% %   merge_assoc([NodeAssoc|NodeAssoc1List],NodeAssoc1),
% %   union_all([CallGraph|CallGraph1List],CallGraph1),
%    put_method_assoc((NewMHash,NewClassName,NewMethodName,NewMSig),NodeAssoc,white,NodeAssoc1,(SuperMHash,SuperClassName,SuperMethodName,SuperMSig)),
%    union(CallGraph,[edge((MHash,ClassName,MethodName,MSig),(SuperMHash,SuperClassName,SuperMethodName,SuperMSig))],CallGraph1),
%    % Non-deterministically explore all inherited (and untrusted) versions of this method
%    (\+get_assoc((DestMHash,DestClassName,DestMethodName,DestMSig),NodeAssoc,_) ->
%        jpl_call(NewM, getInstructionList, [], NewIList),
%        (NewIList \== @null ->
%            jpl_call(NewIList, getStart, [], CalledInstrHandle),
%            format('Method ~w.~w~w entered from ~w.~w~w~n',[NewClassName,NewMethodName,NewMSig,ClassName,MethodName,MSig]),
%            build_callgraph(CalledInstrHandle,NewC,NewM,NodeAssoc1,FinalNodeAssoc,CallGraph1,FinalCallGraph)
%            ;
%            FinalNodeAssoc = NodeAssoc1,
%            FinalCallGraph = CallGraph1))
%    ;
%    FinalNodeAssoc = NodeAssoc,
%    FinalCallGraph = CallGraph).

% put_method_assoc((MHash,CName,MName,MSig),NodeAssoc,Color,NewNodeAssoc,SuperMethod) :-
%    assoc_to_keys(NodeAssoc,NodeKeyList),
%    put_method_assoc(NodeKeyList,(MHash,CName,MName,MSig),NodeAssoc,Color,NewNodeAssoc,SuperMethod).
    
% put_method_assoc([],(MHash,CName,MName,MSig),NodeAssoc,Color,NewNodeAssoc,(MHash,CName,MName,MSig)) :-
%    put_assoc((MHash,CName,MName,MSig),NodeAssoc,Color,NewNodeAssoc).
% put_method_assoc([(OldMHash,OldCName,OldMName,OldMSig)|Keys],(MHash,CName,MName,MSig),NodeAssoc,Color,NewNodeAssoc,SuperMethod) :-
%    atom_concat(OldMName,OldMSig,FullOldMSig),
%    atom_concat(MName,MSig,FullMSig),
%    jpl_call('mcparser.ClassParser',isOverloaded,[OldCName,CName,FullOldMSig,FullMSig],OverloadedCName),
%    (OverloadedCName == @null ->
%        put_method_assoc(Keys,(MHash,CName,MName,MSig),NodeAssoc,Color,NewNodeAssoc,SuperMethod)
%        ;
%        (OverloadedCName == CName ->
%            % The old one overloads this one; fold into the higher-up one
%            remove_assoc(NodeAssoc,(OldMHash,OldCName,OldMName,OldMSig),NodeAssoc1),
%            put_method_assoc(Keys,(MHash,CName,MName,MSig),NodeAssoc1,Color,NewNodeAssoc,SuperMethod)
%            ;
%            % The new one overloads the old one; stop here since we already have the higher-up one
%            NewNodeAssoc = NodeAssoc,
%            SuperMethod = )).
        
% mark_sync_methods(+Class)
%
% Marks all non-constructor methods in Class as sync methods.
mark_sync_methods(C) :-
    jpl_call('mcparser.instr.InstructionInfo',getClassMethodsNoConstructors,[C],MArrayList),
    arraylist_to_list(MArrayList,MList),
    mark_sync_methods_helper(C,MList).
mark_sync_methods_helper(_,[]).
mark_sync_methods_helper(C,[M|Ms]) :-
    jpl_call(C,getClassName,[],CName),
    jpl_call(M,getName,[],MName),
    jpl_call(M,getSignature,[],MSig),
    (sync_method((CName,MName,MSig)) -> true ; assert(sync_method((CName,MName,MSig)))),
    mark_sync_methods_helper(C,Ms).

% mark_recursive_methods(+StartClass,+StartMethod,+NodeAssoc)
%
% The callgraph_edge rules must be given as produced by build_callgraph.
% Using retractall and assert predicates, creates a set of rules
% that inform the verifier which methods are recursive. Such
% methods must be handled separately during verification
% after all other code has finished processing.
mark_recursive_methods(StartC,StartM) :-
    writeln('Marking recursive methods...'),
%    retractall(recursive_method(_)),
    jpl_call(StartC,getClassName,[],StartCName),
    jpl_call(StartM,getName,[],StartMName),
    jpl_call(StartM,getSignature,[],StartMSig),
    empty_assoc(NodeColor),
%    put_assoc((StartCName,StartMName,StartMSig),NodeColor1,gray,NodeColor),
    findall(_,mark_recursive_methods1((StartCName,StartMName,StartMSig),NodeColor),_).
    
mark_recursive_methods1(Method,_) :-
    recursive_method(Method). % No need to explore something we already know to be recursive
mark_recursive_methods1(Method,NodeColor) :-
    \+recursive_method(Method),
    get_assoc(Method,NodeColor,black). % Already explored; ignore
mark_recursive_methods1(Method,NodeColor) :-
    \+recursive_method(Method),
    \+get_assoc(Method,NodeColor,_), % Unexplored
    callgraph_edge(Method,NextMethod),
    put_assoc(Method,NodeColor,gray,NewNodeColor),
    mark_recursive_methods1(NextMethod,NewNodeColor).
mark_recursive_methods1(Method,NodeColor) :-
    \+recursive_method(Method),
    \+get_assoc(Method,NodeColor,_), % Unexplored
    \+callgraph_edge(Method,_NextMethod).
mark_recursive_methods1(Method,NodeColor) :-
    \+recursive_method(Method),
    get_assoc(Method,NodeColor,gray), % This one's recursive; mark it
    assert(recursive_method(Method)).
    
% is_recursive(+ClassName,+MethodName)
%
% Checks to see if either the given method is in fact recursive (based
% on what was marked in mark_recursive_methods), or if it overloads
% a method that was considered recursive.
is_recursive(CName,MName,MSig) :-
%    jpl_call(C,getClassName,[],CName),
%    jpl_call(M,getName,[],MName),
%    jpl_call(M,getSignature,[],MSig),
    recursive_method((CName,MName,MSig)).
%    atom_concat(MName,MSig,FullMSig),
%    findall(RecursiveMethod,recursive_method(RecursiveMethod),RecursiveList),
%    is_recursive_helper(CName,MName,MSig,FullMSig,RecursiveList),!. % Determinism desired here...
    
is_recursive_helper(CName,MName,MSig,_FullMSig,[(CName,MName,MSig)|_RMs]).
is_recursive_helper(CName,MName,MSig,FullMSig,[(RCName,RMName,RMSig)|_RMs]) :-
    atom_concat(RMName,RMSig,FullRMSig),
    jpl_call('mcparser.ClassParser',isOverloaded,[CName,RCName,FullMSig,FullRMSig],RCName),
    assert(recursive_method((CName,MName,MSig))).
is_recursive_helper(CName,MName,MSig,FullMSig,[_|RMs]) :-
    is_recursive_helper(CName,MName,MSig,FullMSig,RMs).


% add_ret_edges(+InstrGraph,+StartIH,-NewInstrGraph)
%
% Handles edges from 'ret' instructions to all possible return
% addresses. Because of the (admittedly low) possibility of
% having strange, exception-driven control flows, we just
% set up nondeterministic edges from every ret instruction
% to every JsrInstruction's (jsr, jsr_w) successor instruction.
% This DOES in effect create the possibility of unintended loops
% and bizarre control flows, but those will largely be wiped
% out in the collapsing analysis.
add_ret_edges(InstrGraph,StartIH,NewInstrGraph) :-
    add_ret_edges1(InstrGraph,StartIH,[],[],NewInstrGraph).
    
add_ret_edges1(InstrGraph,@null,Jsrs,Rets,NewInstrGraph) :-
    % Base case; now we set up links from every Ret to every Jsr
    % in the NewInstrGraph.
    add_ret_edges2(InstrGraph,Jsrs,Rets,NewInstrGraph).
add_ret_edges1(InstrGraph,IH,Jsrs,Rets,NewInstrGraph) :-
    IH \== @null,
    jpl_call(IH,getPosition,[],Offset),
    jpl_call(IH,getInstruction,[],I),
    jpl_call(I,getName,[],IName),
    ((IName == 'jsr' ; IName == 'jsr_w') ->
        NewJsrs = [Offset|Jsrs],
        NewRets = Rets
        ;
        (IName == 'ret' ->
            NewJsrs = Jsrs,
            NewRets = [Offset|Rets]
            ;
            NewJsrs = Jsrs,
            NewRets = Rets)),
    jpl_call(IH,getNext,[],NextIH),
    add_ret_edges1(InstrGraph,NextIH,NewJsrs,NewRets,NewInstrGraph).

add_ret_edges2(FinalInstrGraph,_,[],FinalInstrGraph).
add_ret_edges2(InstrGraph,Jsrs,[Ret|Rets],FinalInstrGraph) :-
    findall((Ret,Jsr),member(Jsr,Jsrs),NewEdges),
    append(NewEdges,InstrGraph,NewInstrGraph),
    add_ret_edges2(NewInstrGraph,Jsrs,Rets,FinalInstrGraph).
    
% collapse_instr_graphs(+Policy,?Safe)
%
% Given prior assertions of method_instr_graph, obtains each graph and collapses
% all unmarked nodes into single nodes. This will result in many methods consisting
% of just one node.
% Note that invokations that are part of control flows leading to marked instructions
% will be maintained.
% Some notes on things that must be checked in this analysis:
% 1. Anything unmarked CANNOT be a security-relevant instruction, so we must check that
% 2. Anything unmarked CANNOT be a "put" instruction that affects a reified state variable
% 3. If we come across an invoke that creates a callback, we must assert that callback for
%    future analysis.
% If either 1 or 2 is found to be an issue, we set Safe=notSafe.
collapse_instr_graphs(Policy,Safe) :-
    retractall(reaches_start_instr(_,_)),
    findall(Safe,
        (method_instr_graph(CName,MSig,StartOffset,OffsetGraph),
         \+collapsed_method_instr_graph(CName,MSig),
         retractall(safely_unmarked(_)),
         retractall(safely_marked(_)),
         collapse_instr_graph(CName,MSig,StartOffset,OffsetGraph,NewOffsetGraph,Policy,Safe),
         retractall(method_instr_graph(CName,MSig,StartOffset,OffsetGraph)),
         assert(method_instr_graph(CName,MSig,StartOffset,NewOffsetGraph)),
         assert(collapsed_method_instr_graph(CName,MSig)),
         garbage_collect_atoms),
        Safes),
        (contains_all_vars(Safes) -> true ; Safe = notSafe).
        
collapse_instr_graph(_,_,_StartOffset,OffsetGraph,OffsetGraph,_,Safe) :- nonvar(Safe),!.
collapse_instr_graph(_,_,_StartOffset,OffsetGraph,OffsetGraph,_,Safe) :- var(Safe),OffsetGraph==[],!.
collapse_instr_graph(CName,MSig,_StartOffset,OffsetGraph,NewOffsetGraph,Policy,Safe) :-
    var(Safe),
    OffsetGraph\==[],
    get_graph_offsets(OffsetGraph,OffsetList),
    format('in collapse_instr_graph, just starting validate_handle_markings for ~w.~w~n',[CName,MSig]),flush_output,
    jpl_call('mcparser.instr.InstructionInfo',getClassGen,[CName],C),
    jpl_call('mcparser.instr.InstructionInfo',getMethodFromClass,[C,MSig],M),
    validate_handle_markings(CName,MSig,C,M,Policy,OffsetList,Safe),
    format('in collapse_instr_graph, just finished validate_handle_markings for ~w.~w; Safe = ~w~n',[CName,MSig,Safe]),flush_output,
    collapse_instr_graph1(CName,MSig,OffsetList,OffsetGraph,[],CollapsedOffsetGraph),
    format('in collapse_instr_graph, just finished collapse_instr_graph1 for ~w.~w~n',[CName,MSig]),flush_output,
%    remove_unreachable_nodes(IHList,StartIH,CollapsedIHGraph,StartIHGraph),
%    format('in collapse_instr_graph, just finished remove_unreachable_nodes (start) for ~w.~w~n',[CName,MSig]),flush_output,
    % Need to also start from every exception handler, since they aren't
    % reached through the graph directly
%    findall(NewIHGraph1,
%        (method_exception_handler(CName,MSig,ExceptionIH,_,_,_),
%         remove_unreachable_nodes(IHList,ExceptionIH,CollapsedIHGraph,NewIHGraph1),
%    format('in collapse_instr_graph, just finished remove_unreachable_nodes (exception) for ~w.~w~n',[CName,MSig]),flush_output
%         ),
%        ExceptionIHGraphs),
%    format('in collapse_instr_graph, just finished remove_unreachable_nodes (exceptions) for ~w.~w~n',[CName,MSig]),flush_output,
%    flatten([StartIHGraph|ExceptionIHGraphs],FlatIHGraphs),
%    list_to_set(FlatIHGraphs,NewIHGraph),
    % NewIHGraph = StartIHGraph,
    NewOffsetGraph = CollapsedOffsetGraph.
%   format('InstrGraph for ~w.~w:~n~w~n',[CName,MSig,NewIHGraph]),
%   findall(_,(member(IH,IHList),jpl_call(IH,toString,[@false],IHToString),format('~w ---- ~w~n',[IHToString,IH])),_).

% Current algorithm:
% For each marked node in the graph, backtrack to see if there is a path to it
% from either (1) the start node, (2) an exception handler node, or
% (3) a "departure" node (unmarked nodes which succeed marked ones).
% For each such path, create a direct edge between the two nodes involved.
% Also copy over any existing outgoing edges from marked nodes.
% In effect, this will remove all unmarked nodes except for the entrypoint node, exception handler nodes,
% and all "departure nodes" (nodes immediately adjacent to marked nodes, which force a SYNC check).
collapse_instr_graph1(_,_,[],_,FinalOffsetGraph,FinalOffsetGraphSet) :-
    list_to_set(FinalOffsetGraph,FinalOffsetGraphSet).
collapse_instr_graph1(CName,MSig,[Offset|Offsets],OffsetGraph,CurOffsetGraph,FinalOffsetGraph) :-
    (is_marked(CName,MSig,Offset) ->
        % Marked: Copy over all outgoing edges, then create
        % incoming edges from every node to which we can backtrack
        % that fulfills one of the three conditions described above.
        findall((Offset,NextOffset),member((Offset,NextOffset),OffsetGraph),OutgoingEdges),
        backtrack_to_significant_nodes(CName,MSig,Offset,OffsetGraph,IncomingEdges),
        append(OutgoingEdges,IncomingEdges,NewEdges),
        list_to_set(NewEdges,NewEdgesSet),
        append(NewEdgesSet,CurOffsetGraph,NewOffsetGraph)
        ;
        ((method_instr_graph(CName,MSig,Offset,_); % Is a start node
          method_exception_handler(CName,MSig,Offset,_,_,_);
          return_node(CName,MSig,Offset)) ->
            % Significant but not marked: Get every incoming edge from other
            % significant nodes. Usually nothing gets added, but this case
            % is needed for loops and returns.
            backtrack_to_significant_nodes(CName,MSig,Offset,OffsetGraph,IncomingEdges),
            append(IncomingEdges,CurOffsetGraph,NewOffsetGraph)
            ;
            % Unmarked: Do nothing
            NewOffsetGraph = CurOffsetGraph)),
    collapse_instr_graph1(CName,MSig,Offsets,OffsetGraph,NewOffsetGraph,FinalOffsetGraph).
    
% backtrack_to_significant_nodes(+CName,+MSig,+Offset,+OffsetGraph,-IncomingEdges)
%
% Takes every possible path back up from the current IH through the IHGraph,
% terminating at any node considered "significant"; a linking edge is created
% in IncomingEdge from each such node to the original IH.
% Nodes considered "significant" include:
% 1. Start nodes
% 2. Exception handler nodes
% 3. Marked nodes
% 4. "Departure" nodes (Unmarked nodes which succeed marked ones)
backtrack_to_significant_nodes(CName,MSig,Offset,OffsetGraph,IncomingEdges) :-
    findall(IncomingEdge,
            backtrack_to_significant_nodes1(CName,MSig,Offset,Offset,OffsetGraph,OffsetGraph,IncomingEdge),
            IncomingEdges).
            
backtrack_to_significant_nodes1(CName,MSig,OriginOffset,CurOffset,OffsetGraph,FullOffsetGraph,IncomingEdge) :-
    \+backtracked_offset(CName,MSig,OriginOffset,CurOffset),
    assert(backtracked_offset(CName,MSig,OriginOffset,CurOffset)),
    select((SourceOffset,CurOffset),OffsetGraph,SelectedGraph),
    ((method_instr_graph(CName,MSig,SourceOffset,_); % Start node
      method_exception_handler(CName,MSig,SourceOffset,_,_,_); % Exception handler node
      is_marked(CName,MSig,SourceOffset); % Marked node
      (member((MarkedOffset,SourceOffset),FullOffsetGraph),is_marked(CName,MSig,MarkedOffset))) -> % Departure node
        % SourceIH is a significant node. Create a link and stop here.
        IncomingEdge = (SourceOffset,OriginOffset)
        ;
        % Keep going up the path...
        backtrack_to_significant_nodes1(CName,MSig,OriginOffset,SourceOffset,SelectedGraph,FullOffsetGraph,IncomingEdge)).
    
% Current algorithm:
% For each unmarked node in the graph, get a list of every marked node it can reach without
% going through another marked node. Put an edge in our collapsed graph for every
% such pair.
% Also, keep every transition that starts with a marked node from the original graph.
% Finally, perform a reachability analysis to remove all unreachable nodes.
% In effect, this will remove all unmarked nodes except for the entrypoint node
% and all "departure nodes" (nodes immediately adjacent to marked nodes, which force a SYNC check).
% (Note: As a kluge to avoid exception control flow issues, we treat the beginnings of exception
% handlers as if they are marked.)
collapse_instr_graph1_old(_,_,[],_,FinalIHGraph,FinalIHGraph).
collapse_instr_graph1_old(CName,MSig,[IH|IHs],IHGraph,CurIHGraph,FinalIHGraph) :-
    ((is_marked(CName,MSig,IH);method_exception_handler(CName,MSig,IH,_,_,_)) ->
        % Marked: keep every outgoing transition.
        findall((IH,NextIH),member((IH,NextIH),IHGraph),NewEdges),
        append(NewEdges,CurIHGraph,NewIHGraph)
        ;
        % Unmarked: Build connections to every reachable marked node
        get_edges_to_marked_nodes(CName,MSig,IH,IHGraph,NewEdges),
        append(NewEdges,CurIHGraph,NewIHGraph)),
    collapse_instr_graph1_old(CName,MSig,IHs,IHGraph,NewIHGraph,FinalIHGraph).

% remove_unreachable_nodes(+NodeList,+Start,+Graph,-FinalGraph)
%
% Performs a reachability analysis and removes all unreachable nodes.
remove_unreachable_nodes(NodeList,Start,Graph,FinalGraph) :-
    remove_unreachable_nodes(NodeList,Start,Graph,Graph,FinalGraph).
    
remove_unreachable_nodes([],_,_,FinalGraph,FinalGraph).
remove_unreachable_nodes([Node|Nodes],Start,Graph,CurGraph,FinalGraph) :-
    (backtracks_to_start(Node,Start,Graph) ->
        (\+backtracks_to_instr(Node,Start) ->
            assert(backtracks_to_instr(Node,Start))
            ;
            true),
        NewGraph = CurGraph
        ;
        delete(CurGraph,(Node,_),NewGraph1),
        delete(NewGraph1,(_,Node),NewGraph)),
    remove_unreachable_nodes(Nodes,Start,Graph,NewGraph,FinalGraph).
 
backtracks_to_start(Start,Start,_Graph).
backtracks_to_start(Node,Start,_Graph) :-
    Node \= Start,
    backtracks_to_instr(Node,Start).
backtracks_to_start(Node,Start,Graph) :-
    Node \= Start,
    \+backtracks_to_instr(Node,Start),
    select((PrevNode,Node),Graph,SelectedGraph),
    backtracks_to_start(PrevNode,Start,SelectedGraph),!.
     
% get_edges_to_marked_nodes(+CName,+MSig,+IH,+IHGraph,-NewEdges)
%
% Does a traversal analysis to find every reachable marked node (without
% going through any other marked nodes).
get_edges_to_marked_nodes(CName,MSig,IH,IHGraph,NewEdges) :-
    findall(NewEdges1,get_edges_to_marked_nodes(CName,MSig,IH,IH,IHGraph,[],NewEdges1),NewEdges2),
    flatten(NewEdges2,NewEdges3),
    list_to_set(NewEdges3,NewEdges),
    (\+edges_to_marked_nodes(IH,_) ->
        list_2nd(NewEdges,NewEdges2nds),
        assert(edges_to_marked_nodes(IH,NewEdges2nds))
        ;
        true).

get_edges_to_marked_nodes(_,_,OrigIH,IH,_,_,NewEdges) :-
    edges_to_marked_nodes(IH,Dests),
    findall((OrigIH,Dest),member(Dest,Dests),NewEdges),!.
get_edges_to_marked_nodes(_,_,_,IH,IHGraph,_,[]) :-
    \+edges_to_marked_nodes(IH,_),
    \+member((IH,_),IHGraph).
get_edges_to_marked_nodes(_,_,_,IH,IHGraph,SeenEdges,[]) :-
    \+edges_to_marked_nodes(IH,_),
    member((IH,NextIH),IHGraph),
    member((IH,NextIH),SeenEdges).
get_edges_to_marked_nodes(CName,MSig,OrigIH,IH,IHGraph,SeenEdges,NewEdges) :-
    \+edges_to_marked_nodes(IH,_),
    member((IH,NextIH),IHGraph),
    \+member((IH,NextIH),SeenEdges),
    SeenEdges1 = [(IH,NextIH)|SeenEdges],
    (is_marked(CName,MSig,NextIH) ->
        NewEdges = [(OrigIH,NextIH)]
        ;
        findall(NewEdges1,get_edges_to_marked_nodes(CName,MSig,OrigIH,NextIH,IHGraph,SeenEdges1,NewEdges1),NewEdges2),
        flatten(NewEdges2,NewEdges),
        list_2nd(NewEdges,NewEdges2nds),
        assert(edges_to_marked_nodes(IH,NewEdges2nds))).
    
% get_graph_offsets(+OffsetGraph,-OffsetList)
%
% Given an Instruction Offset Graph OffsetGraph (list of offset pairs represented as a digraph),
% extracts a list of every distinct offset in the graph.
get_graph_offsets(OffsetGraph,OffsetList) :- get_graph_offsets(OffsetGraph,[],OffsetList).
get_graph_offsets([],OffsetList,OffsetList).
get_graph_offsets([(Offset,NextOffset)|OffsetGraph],OffsetList,FinalOffsetList) :-
    (member(Offset,OffsetList) ->
        OffsetList1 = OffsetList
        ;
        OffsetList1 = [Offset|OffsetList]),
    (member(NextOffset,OffsetList) ->
        OffsetList2 = OffsetList1
        ;
        OffsetList2 = [NextOffset|OffsetList1]),
    get_graph_offsets(OffsetGraph,OffsetList2,FinalOffsetList).
    
% validate_handle_markings(+ClassName,+MethodWithSig,+Class,+Method,+Policy,+OffsetList,?Safe)
%
% 1. For every unmarked handle, confirms that they are in fact not policy-relevant.
%    (Meaning it is neither a security-relevant instruction nor is it a put field
%    operation that acts on a reified state variable)
% 2. If we reach an unmarked invoke, we check to see if it has a control flow to
%    a method containing marked code; if so, we explicitly mark it ourselves so
%    it doesn't get removed during graph collapsing.
% 3. If we come across an invoke that generates a callback, add that callback into
%    our "sync methods" list for future analysis. (This part was shoehorned in
%    when we added the graph collapsing; it used to be in the normal analysis, but
%    we have to get this information before nodes start getting removed)
validate_handle_markings(_,_,_,_,_,[],_Safe) :-
    garbage_collect,
    garbage_collect_atoms.
validate_handle_markings(CName,MSig,C,M,Policy,[Offset|Offsets],Safe) :-
    % Get the instruction handle
    jpl_call('mcparser.instr.InstructionInfo',getIH,[M,Offset],IH),

    % Part 1
    % Are we marked, or are we safely unmarked?
    (is_marked(CName,MSig,Offset) ->
        is_safely_marked(CName,MSig,C,M,IH,Policy,Safe)
        ;
        is_safely_unmarked(CName,MSig,C,M,IH,Policy,Safe)),
    
    % Part 2
    % Is this an invoke?
    % If an unmarked invoke, check to see if it or any overloaded versions of the called method
    % leads into a control flow that reaches an actual marked instruction.
    % If so, we artificially mark this instruction.
    (jpl_call('mcparser.instr.InstructionInfo',isInvoke,[IH],@true) ->
        jpl_call('mcparser.instr.InstructionInfo',getInvokeDataLite,[C,M,IH],IHInvokeData),
        jpl_get(IHInvokeData,className,IHInvokeCName),
        ((var(MarkedIH),\+trusted_class(IHInvokeCName)) ->
            jpl_get(IHInvokeData,methodName,IHInvokeMName),
            jpl_get(IHInvokeData,signature,IHInvokeMSig),
            jpl_call(M,getName,[],MName),
            jpl_call(M,getSignature,[],MShortSig),
            ((callgraph_edge((CName,MName,MShortSig),(IHInvokeCName1,IHInvokeMName,IHInvokeMSig)),
              (IHInvokeCName1 == IHInvokeCName ; implemented_by(IHInvokeCName,IHInvokeCName1)),
              reaches_marked_method((IHInvokeCName1,IHInvokeMName,IHInvokeMSig))) ->
                atom_concat(CName,'.',FullMSig1),
                atom_concat(FullMSig1,MSig,FullMSig),
                jpl_call(IH,getPosition,[],IHOffset),
                jpl_call(IH,toString,[@false],IHToString),
                format('~w in ~w~n',[IHToString,FullMSig]),
                assert(marked_instruction_range(FullMSig,IHOffset,IHOffset)),
                MarkedIH = true
                ;
                true)
            ;
            true)
        ;
        true),
        
    % Part 3
    % Are we at an EventListener or Runnable constructor?
    % We need to handle this here in case we end up removing the invokation.
    % (Deprecated now because we cover all methods in the program)
%    (nonvar(IHInvokeData) ->
%        ((\+know_if_callback(IHInvokeCName),
%          \+trusted_class(IHInvokeCName),
%          format('Checking if ~w is a callback...~n',[IHInvokeCName]),
%          (implemented_by('java.util.EventListener',IHInvokeCName);
%           implemented_by('java.lang.Runnable',IHInvokeCName)),
%          jpl_call('mcparser.instr.InstructionInfo',getClassGen,[IHInvokeCName],IHInvokeC),
%          IHInvokeC \== @null,
% %          (jpl_call('mcparser.instr.InstructionInfo',implementsInterface,[IHInvokeC,'java.util.EventListener'],@true);
% %           jpl_call('mcparser.instr.InstructionInfo',implementsInterface,[IHInvokeC,'java.lang.Runnable'],@true)),
%          format('~w is a callback. Marking.~n',[IHInvokeCName])) ->
%            mark_sync_methods(IHInvokeC),
%            garbage_collect_atoms,
%            assert(know_if_callback(IHInvokeCName))
%            ;
%            assert(know_if_callback(IHInvokeCName)))
%        ;
%        true),
        
    % Part 4
    % Are we marked and in a non-Policy <clinit>? If so, we consider this a policy violation.
    % (Note that this effectively says that if a <clinit> leads into a control flow that hits
    % a marked region, that is also rejected due to part 2)
    %
    % (Handled in Part 1 now, and more accurately, since we care about security-relevant
    % instructions, not all marked ones)
%    ((is_marked(CName,MSig,Offset),
%      MSig == '<clinit>()V') ->
%        Safe = notSafe
%        ;
%        true),
        
    % Recursively go through all the rest of the IHs
    validate_handle_markings(CName,MSig,C,M,Policy,Offsets,Safe).
        

% is_marked(+ClassName,+MethodSig,+Offset)
% is_marked(+ClassName,+MethodSig)
%
% Succeeds if the instruction at the Offset is "marked" (meaning security-relevant).
% The second rule just checks if anything within the given method is marked.
is_marked(CName,_,_) :-
    marked_instruction_class(CName),!.
is_marked(CName,MethodSig,Offset) :-
    atom_concat(CName,'.',FullMethodSig1),
    atom_concat(FullMethodSig1,MethodSig,FullMethodSig),
    marked_instruction_range(FullMethodSig,StartOffset,EndOffset),
    Offset>=StartOffset,
    EndOffset>=Offset,!.

is_marked(CName,_) :-
    marked_instruction_class(CName),!.
is_marked(CName,MethodSig) :-
    atom_concat(CName,'.',FullMethodSig1),
    atom_concat(FullMethodSig1,MethodSig,FullMethodSig),
    marked_instruction_range(FullMethodSig,_,_),!.

% Marked instructions are allowed in <clinit> methods, but not security-relevant ones.
is_safely_marked(_,_,_,_,IH,_,_) :-
    jpl_call(IH,getPosition,[],Offset),
    safely_marked(Offset),!. % Already handled
is_safely_marked(_,MSig,_,_,_,_,_) :-
    MSig \== '<clinit>()V',!.
is_safely_marked(_,'<clinit>()V',C,M,IH,Policy,Safe) :-
    % Check to see if it matches any pointcuts (and thus has
    % transition information)
    jpl_call(M,getArgumentNames,[],ArgArray),
    jpl_call('mcparser.PolicyParser',getTransData,[Policy,IH,C,M,ArgArray,'_'],TransData),
    (jpl_call(TransData,isEmpty,[],@false) ->
        jpl_call(IH,toString,[@false],IHToString),
        format('UNSAFE: The following instruction is unmarked but security-relevant: ~w~n',[IHToString]),
        Safe = notSafe % Security-relevant!
        ;
        % Safe!
        jpl_call(IH,getPosition,[],Offset),
        assert(safely_marked(Offset))).

% is_safely_unmarked(+ClassName,+MethodSig,+Class,+Method,+InstructionHandle,+Policy,?Safe)
%
% Checks to make sure an instruction is in no way security-relevant.
% This includes both it matching a pointcut in the policy and it accessing
% a reified security state variable. Succeeds only if instruction is safely unmarked.
is_safely_unmarked(_,_,_,_,IH,_,_) :-
    jpl_call(IH,getPosition,[],Offset),
    safely_unmarked(Offset),!. % Already handled
is_safely_unmarked(_CName,_MSig,C,M,IH,Policy,Safe) :-
    % First check to see if it matches any pointcuts (and thus has
    % transition information)
    jpl_call(M,getArgumentNames,[],ArgArray),
    jpl_call('mcparser.PolicyParser',getTransData,[Policy,IH,C,M,ArgArray,'_'],TransData),
    (jpl_call(TransData,isEmpty,[],@false) ->
        jpl_call(IH,toString,[@false],IHToString),
        format('UNSAFE: The following instruction is unmarked but security-relevant: ~w~n',[IHToString]),
        Safe = notSafe % Security-relevant!
        ;
        % Second, see if this is a field put operation on a reified state variable
        % (Note: get and ensuing local variable operations are not really a problem;
        % during normal analysis, any put operation using a variable which exists prior
        % to the marked region will be treated as a variable, i.e., unknowable)
        ((jpl_call('mcparser.instr.InstructionInfo',isPutField,[IH],@true),
          jpl_call('mcparser.instr.InstructionInfo',getFieldOpDataLite,[C,M,IH],FieldOpData),
          jpl_get(FieldOpData,className,FieldClassName),
          jpl_get(FieldOpData,fieldName,FieldName),
          is_state_var(FieldClassName,FieldName,_,[],_,_)) ->
            jpl_call(IH,toString,[@false],IHToString),
            format('UNSAFE: The following instruction is unmarked but acts on a reified state variable: ~w~n',[IHToString]),
            Safe = notSafe % Put on a state variable!
            ;
            % Safe!
            jpl_call(IH,getPosition,[],Offset),
            assert(safely_unmarked(Offset)))).

% reaches_marked_method(+(CName,MName,MSig))
%
% Traverses the call graph, starting at the given method, and succeeds if a method
% containing marked code is reached. Note that recursive methods are ignored.
reaches_marked_method(Method) :-
    \+recursive_method(Method),
    Method = (CName,MName,MSig),
    atom_concat(CName,'.',FullMSig1),
    atom_concat(FullMSig1,MName,FullMSig2),
    atom_concat(FullMSig2,MSig,FullMSig),
    % Already figured out the status of this method?
    \+method_reaches_no_marked_code(FullMSig),
    (method_reaches_marked_code(FullMSig) ->
        true
        ;
        % Marked?
        ((marked_instruction_range(FullMSig,_,_);marked_instruction_class(CName)) ->
            format('Marked code in ~w reached by',[FullMSig]),
            true
            ;
            % No contained marked code; recursively traverse anything else we can reach
            callgraph_edge(Method,NextMethod),
            (reaches_marked_method(NextMethod) ->
                (\+method_reaches_marked_code(FullMSig) ->
                    assert(method_reaches_marked_code(FullMSig))
                    ;
                    true),
                !
                ;
                assert(method_reaches_no_marked_code(FullMSig)),
                fail))).

% get_init_instr(+ClassGen,+MethodGen,-StartIH)
%
% Obtains the starting Instruction Handle from the control flow graph
% for the provided method.
get_init_instr(C,M,StartIH) :-
    jpl_call(C,getClassName,[],CName),
    jpl_call(M,getName,[],MName),
    jpl_call(M,getSignature,[],MSig),
    atom_concat(MName,MSig,MFullSig),
    method_instr_graph(CName,MFullSig,StartOffset,_),
    jpl_call('mcparser.instr.InstructionInfo',getIH,[M,StartOffset],StartIH).
        
% get_next_instr(+ClassGen,+MethodGen,+InstructionHandle,-NextInstructionHandle)
% get_next_instr(+ClassGen,+MethodGen,+InstructionHandle,+BranchTaken,-NextInstructionHandle)
%
% Nondeterministically obtains the next instruction in the control flow graph.
% The second rule only truly applies to marked (non-SYNC) instructions, and takes
% only the true or false branch of a conditional.
% For both rules, if an outgoing edge cannot be found, @null is returned.
get_next_instr(C,M,IH,NextIH) :-
    jpl_call(C,getClassName,[],CName),
    jpl_call(M,getName,[],MName),
    jpl_call(M,getSignature,[],MSig),
    atom_concat(MName,MSig,MFullSig),
    jpl_call(IH,getPosition,[],Offset),
    method_instr_graph(CName,MFullSig,_,OffsetGraph),
    ((member((Offset,NextOffset),OffsetGraph),
      NextOffset \== @null) *-> % The "*->" allows backtracking; "->" does not
        jpl_call('mcparser.instr.InstructionInfo',getIH,[M,NextOffset],NextIH)
        ;
        NextIH = @null).
        
get_next_instr(C,M,IH,BranchTaken,NextIH) :-
    BranchTaken \== true ->
        % False branch, meaning the next successive instruction
        % We succeed here iff we get the same handle whether
        % we refer to the graph or the next entry in the InstructionList.
        % Note that if we call this on an unmarked instruction, the graph
        % collapsing algorithm performed earlier causes the results here
        % to be unpredictable.
        jpl_call(IH,getNext,[],FalseIH1),
        jpl_call(FalseIH1,getPosition,[],FalseOffset),
        get_next_instr(C,M,IH,FalseIH2),
        jpl_call(FalseIH2,getPosition,[],FalseOffset),!,
        NextIH = FalseIH2
        ;
        % True branch, meaning something other than the next successive
        % instruction. We succeed here iff we do NOT get the same handle
        % from both the graph and the next entry in the InstructionList.
        % Again, the graph collapsing algorithm makes this unpredictable
        % for unmarked instructions.
        jpl_call(IH,getNext,[],FalseIH),
        jpl_call(FalseIH,getPosition,[],FalseOffset),
        get_next_instr(C,M,IH,TrueIH),
        jpl_call(TrueIH,getPosition,[],TrueOffset),
        FalseOffset \== TrueOffset,!,
        NextIH = TrueIH.
        
% assert_exception_handlers(+CName,+MethodFullSig,+MethodGen)
%
% Asserts facts for method_exception_handler/6, defining
% exception handler information for future use. Also asserts
% that these handlers are marked (so they aren't removed).
assert_exception_handlers(CName,MFullSig,M) :-
    format('assert_exception_handlers for ~w.~w -- ~w~n',[CName,MFullSig,M]),
    jpl_call(M,getExceptionHandlers,[],ExceptionGens),
    jpl_array_to_list(ExceptionGens,ExceptionGensList),
    assert_exception_handlers1(CName,MFullSig,ExceptionGensList).

assert_exception_handlers1(_,_,[]).
assert_exception_handlers1(CName,MFullSig,[Exception|Exceptions]) :-
    jpl_call(Exception,getHandlerPC,[],HandlerIH),
    jpl_call(HandlerIH,getPosition,[],HandlerOffset),
    jpl_call(Exception,getCatchType,[],ExceptionType),
    jpl_call(Exception,getStartPC,[],StartIH),
    jpl_call(Exception,getEndPC,[],EndIH),
    jpl_call(StartIH,getPosition,[],StartOffset),
    jpl_call(EndIH,getPosition,[],EndOffset),
%    jpl_call(HandlerIH,getPosition,[],HandlerOffset),
    assert(method_exception_handler(CName,MFullSig,HandlerOffset,ExceptionType,StartOffset,EndOffset)),
    format('asserting method_exception_handler(~w,~w,~w,~w,~w,~w)~n',[CName,MFullSig,HandlerOffset,ExceptionType,StartOffset,EndOffset]),
%    atom_concat(CName,'.',FullSig1),
%    atom_concat(FullSig1,MFullSig,FullSig),
%    assert(marked_instruction_range(FullSig,HandlerOffset,HandlerOffset)),
    assert_exception_handlers1(CName,MFullSig,Exceptions).