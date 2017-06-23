:-['utility'].
:-['callgraph'].

process_classes([]).
process_classes([C|CList]) :-
	jpl_call('mcparser.instr.InstructionInfo',getClassGen,[C],CGen),
	write(CGen),
	write("\n"),
	%jpl_call('mcparser.instr.InstructionInfo',getClassMethods,[CGen],MArrayList),
    %arraylist_to_list(MArrayList,MList),
	jpl_call('mcparser.ClassParser',createMethodGenArray,[CGen],CMethodGenArray),
	write(CMethodGenArray),
	write("\n"),
	jpl_array_to_list(CMethodGenArray,[MGen1,MGen2|MGenList]),
	writeln([MGen1,MGen2|MGenList]),
	write('\n\n'),
	jpl_call(MGen1,getMethod,[],Method1),
	jpl_call(Method1,getName,[],Naam1),
	jpl_call(Method1,getSignature,[],Sig1),
	atom_concat(Naam1,Sig1,Trial1),
	format('MethodGen1 ~s~n',[Trial1]),
	jpl_call(MGen2,getMethod,[],Method2),
	jpl_call(Method2,getName,[],Naam),
	jpl_call(Method2,getSignature,[],Sig),
	atom_concat(Naam,Sig,Trial),
	format('MethodGen2 ~s~n~n',[Trial]),
	
	jpl_call(MGen1,getInstructionList,[],MIList),
	jpl_call(MIList,getInstructionHandles,[],IHArray),
	jpl_array_to_list(IHArray,[IH|InstructionHandleList]),
	
	jpl_call(MGen1,getLocalVariables,[],LVArray),
	jpl_array_to_list(LVArray,LVList),
	S = state([env(CGen,MGen1,[],LVList,IH)],[]),
	instr(S,NewState).
	%process_methods_in_class(MGenList).
	%process_classes(CList).
	
%% process_methods_in_class([]).
%% process_methods_in_class([MGen1,MGen2|MGenList]) :-
%% 	jpl_call(MGen2,getInstructionList,[],MIList),
%% 	jpl_call(MIList,getInstructionHandles,[],IHArray),
%% 	jpl_array_to_list(IHArray,[IH|InstructionHandleList]),
%% 	write("\n"),
%% 	write("\n"),
%% 	interp(IH).
	%process_methods_in_class(MGenList).

% interp(@null).
% interp(IH):-
	% IH \== @null,
	% jpl_call(IH,getInstruction,[],I),
	% jpl_call(I,getName,[],S),
	% write(S),
	% write("\n"),
	% jpl_call(IH,getNext,[],INext),
	% interp(INext).

instr(state([EE|_EEs],CTriple), NewState) :-
    % Stop if we are at a null instruction handle
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	InstrHandle == @null,
	write('Yesssssssssssssssssss!'),
	NewState = state([],CTriple).
instr(state([EE|EEs],CTriple), NewState) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	InstrHandle \== @null,
	jpl_call(C,getClassName,[],CToString),
    write('here?'),
	jpl_call(M,getName,[],MToString),	
    write('here?'),
	jpl_call(M,getSignature,[],MSigToString),
    atom_concat(MToString,MSigToString,MFullSig),
    atom_concat(CToString,'.',FullMethodName1),
    atom_concat(FullMethodName1,MFullSig,FullMethodName),
    jpl_call(InstrHandle,getPosition,[],InstrOffset),

	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getName, [], Label),
	
	jpl_call('mcparser.instr.InstructionInfo', getInstrType, [InstrHandle], InstrType),
    
    %get_next_instr(C,M,InstrHandle,NextInstrHandle),
    jpl_call(InstrHandle,toString,[@false],IHToString),
	format('OS=~w,LVs=~w,InstrHandle=~s~n~n',[OS,LVs,IHToString]),
    help_instr(InstrType,state([EE|EEs],CTriple),NextState),
    instr(NextState,NewState).
     % instr(NextState, NewState, Policy, Safe).
	 
help_instr(typed, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    typed_instr(Label, state([EE|EEs],CT), State2).
help_instr(local, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	local_instr(Label, state([EE|EEs],CT), State2).
help_instr(branch, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),    
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    branch_instr(Label, state([EE|EEs],CT), State2).
help_instr(return, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),    
	jpl_call(InstrHandle,getInstruction,[],Instruction),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    return_instr(Label, state([EE|EEs],CT), State2).
help_instr(invoke, state([EE|EEs],CT), state([NewMethodEE, ReturnEE|EEs],NewCT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call(M,getMethod,[],Method1),
	jpl_call(Method1,toString,[],MName1),
	format('In help_instr(invoke....}, MethodGen1 (M) is ~s~n',[MName1]),
	
	
	jpl_call(C,getJavaClass,[],JavaClass),
	jpl_call(InstrHandle,getInstruction,[],Instr),
	jpl_call(InstrHandle,toString,[],Name),
	format('InstructionHandle in invoke: ~s~n',Name),
	jpl_call(C,getConstantPool,[],ConstantPoolGen),
	jpl_call(Instr,getMethodName,[ConstantPoolGen],NextMethodName),
	jpl_call(Instr,getSignature,[ConstantPoolGen],NextMethodSignature),
	atom_concat(NextMethodName,NextMethodSignature,MFullSig),
	format('Signature ~s~n',[MFullSig]),
	jpl_call('mcparser.util.Misc',getMethodGen,[JavaClass,MFullSig],MGEn),
	jpl_call(M,getMethod,[],MGenMethod),
	jpl_call(MGEn,equals,[M],Value),
	write(Value),
	((Value == @true) ->
		jpl_call('mcparser.util.Misc',getMethodGen,[JavaClass,'main([Ljava/lang/String;)V'],NewMethodGen);NewMethodGen = MGEn),
	
	% find out the number of arguments and set up the return stack
    %jpl_get(InvokeDataLite, args, ArgArray),
        
    %(Label = invokestatic -> N is ArgListLength ; N is ArgListLength+1),
    %length(OS,OSLength),
    %(OSLength >= N ->
    %        NewLength is N,
    %        length(Prev, NewLength),
    %        append(Prev, NewOS, OS)
    %        ;
    %        NewOS = []),
    jpl_call(NewMethodGen,getInstructionList, [], NewInstructionList),
	jpl_call(NewInstructionList,getInstructionHandles,[],NewMethodInstrHandleArray),
    jpl_array_to_list(NewMethodInstrHandleArray,[NewMethodInstrHandle|NewMethodInstrHandleList]),
	print_instructions_from_handles([NewMethodInstrHandle|NewMethodInstrHandleList]),
	
	jpl_call(Instr,getArgumentTypes,[ConstantPoolGen],ArgArray),
	jpl_array_to_list(ArgArray, ArgList),
    length(ArgList, ArgListLength),
	
	
    jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	jpl_call(NextInstrHandle,getInstruction,[],I),
	jpl_call(I,getName,[],L),
    ReturnEE = env(C, M, NewOS, LVs, NextInstrHandle),
	format('ReturnEE: OS=~w,LVs=~w,InstrHandle=~s~n~n',[NewOS,LVs,L]),

	jpl_call('mcparser.ClassParser',getLocalVariableTypes,[C, NewMethodGen],NewLVTypeArray),
	jpl_array_to_list(NewLVTypeArray, NewLVTypeList),
	length(NewLVTypeList, LVlength),
	format('LVlength = ~w~nArgListLength = ~w~n', [LVlength,ArgListLength]),
	create_local_vars(Label, N, OS, _NewLocalVars, UpdatedNewLocalVars),	

	NewMethodEE = env(C, NewMethodGen, [], UpdatedNewLocalVars, NewMethodInstrHandle),
	jpl_call(NewMethodInstrHandle,getInstruction,[],NI),
	jpl_call(NI,getName,[],NL),
	format('NewMethodEE: OS=~w,LVs=~w,InstrHandle=~w~n~n',[[],UpdatedNewLocalVars,NL]).

print_instructions_from_handles([]).
print_instructions_from_handles([IH|InstructionHandleList]) :-
	jpl_call(IH,getInstruction,[],Instr),
	jpl_call(Instr,getName,[],Name),
	writeln(Name),
	print_instructions_from_handles(InstructionHandleList).
	
create_local_vars(Label, N, OS, NewLocalVars, UpdatedNewLocalVars) :-
	empty_assoc(NewLocalVars),
	(Label = invokestatic -> length(Prev, N); N1 is N, length(Prev, N1)),
    length(OS,OSLength),
    (OSLength >= N ->
        append(Prev, _ChoppedOS, OS)
        ;
        true),
    reverse(Prev, List),
    help_create_local_vars(List, NewLocalVars, UpdatedNewLocalVars).

help_create_local_vars([L1|List], NewLocalVars, UpdatedNewLocalVars) :-
	assoc_to_list(NewLocalVars, NewLocalVarsList),
	(NewLocalVarsList = [] -> NewK is 0;
	max_assoc(NewLocalVars, K, _),
	NewK is K+1),
	put_assoc(NewK, NewLocalVars, L1, TempNewLocalVars),
	help_create_local_vars(List, TempNewLocalVars, UpdatedNewLocalVars).
help_create_local_vars([], LVs, LVs).


typed_instr(iconst_0, State1, State2) :- call_constintload(State1, State2).
local_instr(istore_1, State1, State2) :- call_localstore(State1, State2).
typed_instr(iconst_5, State1, State2) :- call_constintload(State1, State2).
local_instr(istore_0, State1, State2) :- call_localstore(State1, State2).
local_instr(istore_2, State1, State2) :- call_localstore(State1, State2).
typed_instr(iconst_3, State1, State2) :- call_constintload(State1, State2).
local_instr(istore_3, State1, State2) :- call_localstore(State1, State2).
local_instr(iload_2, State1, State2) :- call_localload(State1, State2).
local_instr(iload_3, State1, State2) :- call_localload(State1, State2).
local_instr(iload_1, State1, State2) :- call_localload(State1, State2).
local_instr(aload,State1,State2) :- call_localload(State1,State2).
local_instr(aload_0, State1, State2) :- call_localload(State1, State2).
local_instr(aload_1, State1, State2) :- call_localload(State1, State2).
local_instr(aload_2, State1, State2) :- call_localload(State1, State2).
local_instr(aload_3, State1, State2) :- call_localload(State1, State2).

% In case of normal returns, simply pop the callee execution env
return_instr(return, state([_CalleeEE,CallerEE|EEs],CT), state([NewCallerEE|EEs],CT)) :-
	writeln('coming to first return case'),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
%    get_next_instr(OldC,OldM,OldInstrHandle,NextInstrHandle),
	NewCallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle).
% A return WITHOUT an underlying method
return_instr(_, state([_OldEE],CT), state([FinalEE],CT)) :-
    FinalEE = env(c,m,os,lvs,@null), % setting the next instruction to null means we're at the end
	writeln('bottom-level return').

typed_instr(isub, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
 %%    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	%% Result1 = O2 - O1,
 %%    ((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).

branch_instr('if_icmple', state([EE|EEs],CT), state([PosEE|EEs],NewCT)):-
	writeln('true'),
	EE = env(C, M, OS, LVs, InstrHandle),
    %% (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
	jpl_call(InstrHandle,getTarget,[],NextHandle),
	jpl_call(NextHandle,getInstruction,[],NextInstr),
	jpl_call(NextInstr,getName,[],NextName),
    format('Branch on ~w~n',[IHToString]),
    writeln('True if_icmple branch'),
	write(NextName),
    jpl_call(InstrHandle,getNext,[],PosInstrHandle),
 	PosEE = env(C, M, [], LVs, NextHandle).
	
branch_instr('if_icmple', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	writeln('false'),
	EE = env(C, M, OS, LVs, InstrHandle),
    %% (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	writeln('False if_icmple branch'),	
	%get_next_instr(C,M,InstrHandle,false,NextHandle),
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, [], LVs, NegInstrHandle).

branch_instr('goto', state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle, getTarget, [], BranchInstrHandle),
	(BranchInstrHandle \== @null ->
        jpl_call(BranchInstrHandle,getPosition,[],Offset),
        format('Goto offset ~w~n',[Offset]) ; true),
	NewEE = env(C, M, [], LVs, BranchInstrHandle).

call_constintload(state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getValue, [], Value),
	jpl_call(Value, intValue, [], IntValue),
	NewOS = [IntValue|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).

call_localload(state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    %jpl_call('mcparser.instr.InstructionInfo', getLocalVariableIndex, [InstrHandle], Index),
    %get_assoc(Index, LVs, Value),
	%NewOS = [Value|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS, LVs, NewInstrHandle).

call_localstore(state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    %jpl_call('mcparser.instr.InstructionInfo', getLocalVariableIndex, [InstrHandle], Index),
	%OS = [Value|OS1] ; (OS = [], OS1 = []),
    %put_assoc(Index, LVs, Value, NewLVs),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [], LVs, NewInstrHandle).