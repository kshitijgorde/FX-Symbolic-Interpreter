:-['utility'].
:-['callgraph'].
:-['classlist'].
:- use_module(library(assoc)).

process_classes([]).
process_classes([C|CList]) :-	
	jpl_call('mcparser.instr.InstructionInfo',getClassGen,[C],CGen),		%Cgen is a datastructure from bcel that holds class related info.
	open('Symbolic.txt',write,Out),
	format(Out,'The ClassGen is: ~w~n',CGen),
	%jpl_call('mcparser.instr.InstructionInfo',getClassMethods,[CGen],MArrayList),
    %arraylist_to_list(MArrayList,MList),
	jpl_call('mcparser.ClassParser',createMethodGenArray,[CGen],CMethodGenArray), %returns method array which returns all methods in the given CGen.
	format(Out,'The MethodGenArray retrieved is: ~w~n',CMethodGenArray),
	jpl_array_to_list(CMethodGenArray,[First,MGen1|MGenList]),
	writeln([First,MGen1|MGenList]),
	
	write(Out,'\n\n'),
	jpl_call(MGen1,getMethod,[],Method1),	%MethodGen is not the same as Method (Both are differnce data structures)	..this will be public void init...
	jpl_call(Method1,getName,[],Naam1),
	jpl_call(Method1,getSignature,[],Sig1),
	atom_concat(Naam1,Sig1,Trial1),
	format(Out,'Method name:~w~n',Naam1),
	format(Out,'Its signature is:~w~n',Sig1),	
	format(Out,'MethodGen1 ~s~n',[Trial1]),
	%jpl_call(MGen2,getMethod,[],Method2),
	%jpl_call(Method2,getName,[],Naam),
	%jpl_call(Method2,getSignature,[],Sig),
	%atom_concat(Naam,Sig,Trial),
	%format('MethodGen2 ~s~n~n',[Trial]),
	jpl_call(MGen1,getInstructionList,[],MIList),
	jpl_call(MIList,toString,[],String_MIList),
	format(Out,'The Instruction List is: ~w~n',String_MIList),
	%jpl_call(av,c),
	jpl_call(MIList,getInstructionHandles,[],IHArray),
	jpl_array_to_list(IHArray,[IH|InstructionHandleList]),
	
	jpl_call(MGen1,getLocalVariables,[],LVArray),	%LVArray is a LocalVariableGen[] from bcel library
   	%format('LocalVariable Gen is ~w~n',LVArray),
    jpl_array_to_list(LVArray, LVList),
    list_to_indexed_assoc(LVList, LocalVars),
    format(Out,'Local Variables:~w~n',LocalVars),		% This representation is of the AVL Tree form. See documentation for more.
	OperandStack = [],
	%jpl_call(MGen2,getLocalVariables,[],MLVArray),
    %jpl_array_to_list(MLVArray, MLVList),
    %list_to_indexed_assoc(MLVList, MLocalVars),
	%write(MLocalVars),
	%% open('c:/Users/kshit/Desktop/FX Symbolic Interpreter/Policies.txt',read,Stream),
	%% read(Stream,Policy1),
	%% close(Stream),
	%% write(Policy1),
	S = state([env(CGen,MGen1,OperandStack,LocalVars,IH)],[]),	%The first instruction handle will give you the next one. Hence only the first required
	%verify_inductive(S,Out,Policy1). %Pass formula F
	instr(S,Out,NewState).
	%process_methods_in_class(MGenList).
	%process_classes(CList).


read_file(Stream,[]) :-
    at_end_of_stream(Stream).

read_file(Stream,[X|L]) :-
    \+ at_end_of_stream(Stream),
    read(Stream,X),
    read_file(Stream,L).


verify_inductive(S,Out,and(X,Y)) :- 
% We're verifying that when A= java.net.URL.OpenConnection then we should not allow B=java.lang.Runtime.exec in future
format('Processing Formula'),
verify_inductive(S,Out,X),
\+verify_inductive(S,Out,Y).


verify_inductive(state([EE|EEs],CTriple),Out,exec) :-

EE = env(C,M,OS,LVs,InstrHandle),
format(Out,'Processing in exec',[InstrHandle]),
jpl_call(InstrHandle,toString,[],SInstrHandle),
format(Out,'Printing Instr:~w~n',[SInstrHandle]),
jpl_call('mcparser.instr.InstructionInfo',getInstrType,[InstrHandle],InstrType),
format(Out,'Printing C:~w~n',[C]),
format(Out,'Printing M:~w~n',[M]),
format(Out,'Printing InstrTYPE from EXEC VERIFY:~w~n',[InstrType]),
(InstrType == invoke -> jpl_call('mcparser.instr.InstructionInfo', getInvokeData, [C,M,InstrHandle], InvokeData), 
	jpl_get(InvokeData,methodName,Mname),format(Out,'Priting method name(from exec):~w~n',[Mname]), (Mname==exec -> format(Out,'POLICY VIOLATION!!exec detected..~n~w',[Mname]));false).


verify_inductive(state([EE|EEs],CTriple),Out,openConnection):-
format('~nIn open connection verify'),
EE = env(C,M,OS,LVs,InstrHandle),
jpl_call(InstrHandle,toString,[],SInstrHandle),
format(Out,'Printing Instr:~w~n',[SInstrHandle]),
jpl_call('mcparser.instr.InstructionInfo',getInstrType,[InstrHandle],InstrType),
format(Out,'Printing C:~w~n',[C]),
format(Out,'Printing M:~w~n',[M]),
format(Out,'Printing InstrTYPE VERIFY:~w~n',[InstrType]),

(InstrType == invoke -> jpl_call('mcparser.instr.InstructionInfo', getInvokeData, [C,M,InstrHandle], InvokeData), 
	jpl_get(InvokeData,methodName,Mname),format(Out,'Priting method name:~w~n',[Mname]),(Mname==openConnection -> format(Out,'openConnection detected..~n~w',[Mname]));false).

verify_inductive(S,Out,not(B)) :-
format('~nIn not(B)'),
format(Out,'B is :::~w~n',[B]),
\+verify_inductive(S,Out,B).

verify_inductive(S,Out,f(B)) :-
format('~nIn future event'),
(verify_inductive(S,Out,B) ; verify_inductive(S,Out,x(f(B)))).

verify_inductive(S,Out,x(B)):-
format('~nIn Next event'),
instr(S,Out,NextState),
verify_inductive(NextState,Out,B).


instr(state([EE|_EEs],CTriple),Out, NewState) :-
    % Stop if we're at a null instruction handle
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	InstrHandle == @null,
	write(Out,'~nExecution complete.'),
	NewState = state([],CTriple).
instr(state([EE|EEs],CTriple),Out, NewState) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	InstrHandle \== @null,
	jpl_call(C,getClassName,[],CToString),		% returns a string with class name\

	jpl_call(M,getName,[],MToString),	
	jpl_call(M,getSignature,[],MSigToString),
    atom_concat(MToString,MSigToString,MFullSig),
    atom_concat(CToString,'.',FullMethodName1),
    atom_concat(FullMethodName1,MFullSig,FullMethodName), %FullMethodName example is:	Kshitij.<init>()V
    format(Out,'Full method name is ~w~n',FullMethodName),		
    jpl_call(InstrHandle,getPosition,[],InstrOffset),
   	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getName, [], Label),
	jpl_call(Instr,toString,[],StringInstr),	
	jpl_call('mcparser.instr.InstructionInfo', getInstrType, [InstrHandle], InstrType),
    
    jpl_call(InstrHandle,toString,[@false],IHToString),
	format(Out,'OS=~w,LVs=~w,InstrHandle=~s~n~n, Type ~w~n',[OS,LVs,IHToString,InstrType]),
    help_instr(InstrType,state([EE|EEs],CTriple),Out,NextState),
    instr(NextState,Out,NewState).
    


help_instr(default, state([EE|EEs],CT),Out, State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call(InstrHandle,toString,[],IHToString),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    default_instr(Label, state([EE|EEs],CT),Out, State2).

help_instr(get,state([EE|EEs],CT),Out, State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    get_instr(Label, state([EE|EEs],CT),Out, State2).	 
help_instr(typed, state([EE|EEs],CT),Out, State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    typed_instr(Label, state([EE|EEs],CT),Out, State2).
help_instr(local, state([EE|EEs],CT),Out, State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	local_instr(Label, state([EE|EEs],CT),Out, State2).
	
help_instr(branch, state([EE|EEs],CT),Out, State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),    
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	format(Out,'Label is:~w~n',[Label]),
    branch_instr(Label, state([EE|EEs],CT),Out, State2).
help_instr(return, state([EE|EEs],CT),Out, State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),    
	jpl_call(InstrHandle,getInstruction,[],Instruction),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	format(Out,'Label from return help_instr:~w~n',Label),
    return_instr(Label, state([EE|EEs],CT),Out, State2).

help_instr(put,state([EE|EEs],CT),Out, State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	put_instr(Label, state([EE|EEs],CT),Out, State2).


help_instr(invoke, state([EE|EEs],CT),Out, state(ReturnEEs, CT)) :-
% This help_instr is for trusted classes. In case of trusted classes we do not need NewMethodEE

%\+(cat(X)) is the same as not(cat(X))
EE = env(C,M,OS, LVs, InstrHandle),
jpl_call(C,getClassName,[],KC),
jpl_call(M,getMethod,[],KM),
jpl_call(KM,toString,[],KMn),
jpl_call(InstrHandle,toString,[],ITR),

format(Out,'C is:~w~n',[KC]),
format(Out,'M is:~w~n',[KMn]),
format(Out,'Itr is:~w~n',[ITR]),
jpl_call('mcparser.instr.InstructionInfo', getInvokeData, [C,M,InstrHandle], InvokeData),
jpl_get(InvokeData, className, NewClassName),
trusted_class(NewClassName),
jpl_call(InstrHandle, getInstruction, [], Instr),
jpl_call(Instr, getName, [], Label),

/* find out the number of arguments */
jpl_get(InvokeData, args, ArgArray),
jpl_array_to_list(ArgArray, ArgList),
length(ArgList, ArgListLength),

(Label = invokestatic -> N is ArgListLength ; N is ArgListLength+1),
length(OS,OSLength),


(OSLength >= N ->
    NewLength is N,
    length(Prev, NewLength),
    append(Prev, NewOS, OS)
    ;
    NewOS = []),
        
jpl_get(InvokeData, retType, RetType),
jpl_get(InvokeData, methodName, MethodName),

jpl_get('org.apache.bcel.generic.Type','VOID',VoidType),

(RetType = VoidType -> UpdatedOS = NewOS ; UpdatedOS = [RetType|NewOS]),

format(Out,'Updated OperandStack:~w~n',[UpdatedOS]),	
write(Out,'Processing Trusted Classes for Invoke Instruction'),

write(Out,'invoke, trusted case'),
format(Out,'ClassName = ~w~n', NewClassName),
format(Out,'MethodName = ~w~n', [MethodName]),
 %% (MethodName=='openConnection' -> jpl_get(InvokeData,cgen,CkGen),jpl_get(InvokeData,mgen,MkGen),
 %% 	%Add this classgen and method gen to return EE
 %% 	jpl_call(InstrHandle,getNext,[],NewInstrHandle),
 %% 	ReturnEE = env(CkGen,MkGen,UpdatedOS,LVs,NewInstrHandle),
 %% 	ReturnEEs = [ReturnEE|EEs]
 %% 	;

	%% % This is a trusted class...No we need not invoke it's method. Just populate ReturnEE as the next state.
	%% jpl_call(InstrHandle,getNext,[],NextInstructionHandle),
	%% ReturnEE = env(C,M,UpdatedOS,LVs,NextInstructionHandle),
	%% ReturnEEs = [ReturnEE|EEs]).
jpl_call(InstrHandle,getNext,[],NextInstructionHandle),
ReturnEE = env(C,M,UpdatedOS,LVs,NextInstructionHandle),
ReturnEEs = [ReturnEE|EEs].



help_instr(invoke, state([EE|EEs],CT), Out,state([NewMethodEE, ReturnEE|EEs],NewCT)) :-
% This help_instr is for non-trusted classes. In case of Untrusted classes we need NewMethodEE

%\+(cat(X)) is the same as not(cat(X))
EE = env(C,M,OS, LVs, InstrHandle),
jpl_call('mcparser.instr.InstructionInfo', getInvokeData, [C,M,InstrHandle], InvokeData),	
jpl_call(InstrHandle, getInstruction, [], Instr),
jpl_call(Instr, getName, [], Label),

jpl_get(InvokeData, args, ArgArray),
jpl_array_to_list(ArgArray, ArgList),
length(ArgList, ArgListLength),

(Label = invokestatic -> N is ArgListLength ; N is ArgListLength+1),
length(OS,OSLength),


(OSLength >= N ->
    NewLength is N,
    length(Prev, NewLength),
    append(Prev, NewOS, OS)
    ;
    NewOS = []),
        
jpl_get(InvokeData, retType, RetType),
jpl_get(InvokeData, methodName, MethodName),

	
jpl_get(InvokeData, className, NewClassName),
\+trusted_class(NewClassName),
format(Out,'In untrusted: OS:~w~n',[OS]),
write(Out,'Processing UnTrusted Classes for Invoke Instruction'),
format(Out,'ClassName = ~w~n', NewClassName),
format(Out,'MethodName = ~w~n', MethodName),
jpl_call(InstrHandle,getNext,[],NextInstructionHandle),
jpl_call(NextInstructionHandle,toString,[],String_InstrHandleNext),
format(Out,'Next Instruction is:~w~n',String_InstrHandleNext),
ReturnEE = env(C,M,NewOS,LVs,NextInstructionHandle),

jpl_get(InvokeData, cgen, NewClassGen),
jpl_get(InvokeData, mgen, NewMethodGen),
jpl_call(NewMethodGen,getLocalVariables,[],LVArray),
jpl_array_to_list(LVArray, LVList),
list_to_indexed_assoc(LVList, NewLocalVars),
jpl_call(NewMethodGen,getInstructionList,[],NewMethodGenInstrutionList),
jpl_call(NewMethodGenInstrutionList,toString,[],String_MIList),
format(Out,'The Instruction List is: ~w~n',String_MIList),
jpl_call(NewMethodGenInstrutionList,getInstructionHandles,[],IHArray),
jpl_array_to_list(IHArray,[IH|InstructionHandleList]),
NewMethodEE = env(NewClassGen, NewMethodGen, [], NewLocalVars, IH),
write(Out,'Added new Untrusted Method to the list of Execution Environments.').








print_instructions_from_handles([]).
print_instructions_from_handles([IH|InstructionHandleList]) :-
	jpl_call(IH,getInstruction,[],Instr),
	jpl_call(Instr,getName,[],Name),
	writeln(Name),
	print_instructions_from_handles(InstructionHandleList).

typed_instr(idiv, State1,Out, State2) :- call_idivision(State1, Out,State2).
typed_instr(iconst_0, State1,Out, State2) :- call_constintload(State1,Out, State2).
typed_instr(iconst_5, State1,Out, State2) :- call_constintload(State1, Out,State2).
typed_instr(iconst_3, State1,Out, State2) :- call_constintload(State1,Out, State2).
typed_instr(iconst_2,State1,Out, State2) :- call_constintload(State1,Out, State2).
typed_instr(iconst_1,State1,Out, State2) :- call_constintload(State1,Out, State2).
typed_instr(iconst_4, State1,Out, State2) :- call_constintload(State1,Out, State2).
typed_instr(iconst_m1,State1,Out,State2) :- call_constintload(State1,Out,State2).
typed_instr(lconst_0,State1,Out,State2) :- call_constlongload(State1,Out,State2).
typed_instr(ldc, State1,Out, State2) :- call_constldcload(State1, Out,State2).
typed_instr(sipush, State1,Out, State2) :- call_constintload(State1,Out, State2).
local_instr(istore,State1,Out,State2) :- call_localstore(State1,Out,State2).
local_instr(istore_0, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(istore_1, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(istore_2, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(istore_3, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(lstore,State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(iload_2, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(iload_0, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(iload_3, State1, Out,State2) :- call_localload(State1,Out, State2).
local_instr(iload_1, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(iload,State1,Out,State2) :- call_localload(State1,Out,State2).
local_instr(lload, State1,Out, State2) :- call_localload(State1,Out,State2).
local_instr(lload_0, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(lload_1, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(lload_2, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(lload_3, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(aload,State1,Out,State2) :- call_localload(State1,Out,State2).
local_instr(aload_0, State1,Out, State2) :- call_localload(State1,Out, State2).
local_instr(aload_1, State1,Out, State2) :- call_localload(State1, Out,State2).
local_instr(aload_2, State1, Out,State2) :- call_localload(State1,Out, State2).
local_instr(aload_3, State1, Out,State2) :- call_localload(State1,Out, State2).
local_instr(astore_1, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(astore_2, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(astore_3, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(astore_4, State1,Out, State2) :- call_localstore(State1,Out, State2).
local_instr(astore, State1,Out, State2) :- call_localstore(State1,Out, State2).
get_instr(getstatic, State1,Out, State2) :- call_getstatic(State1,Out, State2).
get_instr(getfield, State1,Out, State2) :- call_getfield(State1,Out, State2).
put_instr(putfield, State1,Out, State2) :- call_putfield(State1,Out, State2).
typed_instr(bipush, State1,Out, State2) :- call_constintload(State1,Out,State2).

local_instr(iinc,state([EE|EEs],CT),Out,state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle,getInstruction,[],Instr),
    jpl_call(Instr,getIncrement,[],Increment),
    jpl_call(Instr,getIndex,[],Index),
    get_assoc(Index,LVs,Value),
    write(Out,'iinc Processed...~n'),
    put_assoc(Index,LVs,(Value+Increment),NewLVs),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
    NewEE = env(C, M, OS, NewLVs, NewInstrHandle).

typed_instr(imul, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	Result1 = O2 * O1,
    ((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).

% In case of normal returns, simply pop the callee execution env
return_instr(return, state([_CalleeEE,CallerEE|EEs],CT),Out, state([NewCallerEE|EEs],CT)) :-
	write(Out,'coming to first return case'),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
%    get_next_instr(OldC,OldM,OldInstrHandle,NextInstrHandle),
	NewCallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
	jpl_call(OldC,toString,[],String_OldC),
	format(Out,'Old C is ~w~n',String_OldC),
	jpl_call(OldM,toString,[],String_OldM),
	format(Out,'Old M is ~w~n',String_OldM),
	jpl_call(OldInstrHandle,toString,[],String_OldInstrHandle),
	format(Out,'Old Instr Handle is ~w~n',String_OldInstrHandle).

% A return WITHOUT an underlying method
return_instr(_, state([_OldEE],CT),Out, state([FinalEE],CT)) :-
    FinalEE = env(c,m,os,lvs,@null), % setting the next instruction to null means we're at the end
	write(Out,'bottom-level return').

return_instr(areturn, state([CalleeEE,CallerEE|EEs],CT),Out, state( [NewCallerEE|EEs],CT)) :-
	CalleeEE = env(_C, M, CalleeOS, LVs, _InstrHandle),
    (CalleeOS = [RetVar|_] ; CalleeOS = []),
    % ToString operations need to generate a mapping so we know what object
    % was used to generate the resulting string
    % (Currently we just want the same old variable)
    ((jpl_call(M,getName,[],'toString')) ->
        get_assoc(0,LVs,ObjectVar),
        RetVar = ObjectVar
        % term_to_atom(ObjectVar,ObjectVarAtom),
        % term_to_atom(RetVar,RetVarAtom),
        % jpl_call('mcparser.ConstraintBuilder',addToStringEntry,[ObjectVarAtom,RetVarAtom],_)
        ;
        true),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
%    get_next_instr(OldC,OldM,OldInstrHandle,NextInstrHandle),
	NewCallerEE = env(OldC, OldM, [RetVar|OldOS], OldLVs, OldInstrHandle).


return_instr(ireturn, state([CalleeEE,CallerEE|EEs],CT), Out,state( [NewCallerEE|EEs],CT)) :-
	CalleeEE = env(_C, _M, CalleeOS, _LVs, _InstrHandle),
    (CalleeOS = [RetVar|_] ; CalleeOS = []),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
%    get_next_instr(OldC,OldM,OldInstrHandle,NextInstrHandle),
	NewCallerEE = env(OldC, OldM, [RetVar|OldOS], OldLVs, OldInstrHandle).





typed_instr(bastore,state([EE|EEs],CT),Out,state([NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
    EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_ByteOrBoolean,_Index,_Value|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle).

typed_instr(aastore,state([EE|EEs],CT),Out, state([NewEE|EEs],CT)) :-
	write(Out,'Processing aastore........'),
	EE = env(C,M,OS,LVs,InstrHandle),
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	NewEE = env(C,M,OS,LVs,NextInstrHandle).

typed_instr(ishl, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1,_O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [_Result|OS1], LVs, NewInstrHandle).


typed_instr(i2b, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
   	jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS, LVs, NewInstrHandle).

typed_instr(i2l, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS, LVs, NewInstrHandle).
typed_instr(l2i, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS, LVs, NewInstrHandle).
typed_instr(i2s, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS, LVs, NewInstrHandle).
typed_instr(s2i, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS, LVs, NewInstrHandle).
typed_instr(ladd, State1,Out, State2) :- typed_instr(iadd,State1,Out,State2).
typed_instr(iadd, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	Result1 = O2 + O1,
    ((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).

typed_instr(aconst_null, state([EE|EEs],CT),Out, state([NewEE|EEs],CT)) :-
	% Push a null reference onto the stack
	EE = env(C,M,OS,LVs,InstrHandle),
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	NewOS = [null|OS],
	NewEE = env(C,M,NewOS,LVs, NextInstrHandle),
	format(Out,'In aconst_null, NewEE is :NewOS=~w , NextInstrHandle = ~w',[NewOS,NextInstrHandle]).


typed_instr(iastore,state([EE|EEs],CT),Out,state([NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
    EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_Int,_Index,_Value|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle, getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle),
	write(Out,'iastore instruction Processed~n').


typed_instr(anewarray,state([EE|EEs],CT),Out, state([NewEE,EEs],CT)) :-
	EE = env(C,M,OS,LVs,InstrHandle),
	OS = [OS1|RemOS],
	format(Out,'In anewarray OS:~w~n',[RemOS]),
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	jpl_call(NextInstrHandle,getInstruction,[],Instruction),
	jpl_call(Instruction,toString,[],String_Instruction),
	format(Out,'Next Instruction is: ~w~n',String_Instruction),
	NewEE = env(C,M,RemOS,LVs,NextInstrHandle).


typed_instr(new, state([EE|EEs],CT),Out, state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getTypedParam, [C, InstrHandle], Type),
	jpl_call(Type,toString,[],String_Type),
	format(Out,'The Type retrieved is: ~w~n',String_Type),
	jpl_call('mcparser.instr.InstructionInfo', getClassFromType, [Type], RelevantClassGen),
    (RelevantClassGen \== @null ->
        jpl_call(RelevantClassGen, getClassName, [], ClassName)
        ;
        writeln('Could not obtain class definition'),
        ClassName = '?'),
    NewOS = [classname(ClassName)|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).


typed_instr(isub, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	Result1 = O2 - O1,
    ((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).

default_instr(arraylength, state([EE|EEs],CT), Out,state( [NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_Array|OS1] ; (OS = [],OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [_ArrayLength|OS1], LVs, NewInstrHandle).

default_instr(newarray, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
	write(Out,'Processing newarray Instruction~n'),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_ArrayLength|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, ['array_primitive'|OS1], LVs, NewInstrHandle).
default_instr(dup, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	%Duplicates the value on top of the stack....
	write(Out,'Processing dup instruction..'),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [O1,O1|OS1], LVs, NewInstrHandle).


default_instr(pop, state([EE|EEs],CT),Out, state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1|OS1] ; (OS = [] ; OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle).
%-------------- For branch instruction you have to take 2 branches. Condition Positive and Condition Negative

%------------ Kshitij G. Edited for Branch
branch_instr('iflt', state([EE|EEs],CT), Out,state([PosEE,NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format(Out,'Branch on ~w~n',[IHToString]),
%	format('True iflt branch, [O] = [~w]~n',[O]),
	jpl_call(InstrHandle, getTarget,[],PosInstrHandle),
	jpl_call(PosInstrHandle,toString,[],Target_String),
	format(Out,'Target is:~w~n',[Target_String]),
	write(Out,'Positive EE added........~n'),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle),
	jpl_call(InstrHandle, getNext,[],NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle),
	write(Out,'Negative EE EE added........').
		
	
branch_instr('ifnonnull', state([EE|EEs],CT), Out,state([PosEE,NegEE|EEs],NewCT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    jpl_call(InstrHandle, getTarget,[],PosInstrHandle),
	jpl_call(PosInstrHandle,toString,[],Target_String),
	format(Out,'Target is:~w~n',[Target_String]),
	write(Out,'Positive EE added........~n'),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	jpl_call(InstrHandle, getNext,[],NegInstrHandle),
	write(Out,'Negative EE EE added........'),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).
	


%-------------------------------------------------------------------------------------------------


%------------ Kshitij G. Edited for Branch
branch_instr(if_icmple, state([EE|EEs],CT),Out, state([PosEE,NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
	jpl_call(InstrHandle,getTarget,[],NextHandle),
	jpl_call(NextHandle,getInstruction,[],NextInstr),
	jpl_call(NextInstr,getName,[],NextName),
    format(Out,'Branch on ~w~n',[IHToString]),
    writeln(Out,'True if_icmple branch'),
    write(Out,'For if_icmple Ive added the Positive Execution Environment'),
	write(NextName),
    PosEE = env(C, M, OS1, LVs, NextHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	jpl_call(InstrHandle,toString,[@false],IHToString),
    format(Out,'Branch on ~w~n',[IHToString]),
	writeln(Out,'False if_icmple branch'),	
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	write(Out,'For if_icmple Ive added the Negative Execution Environment'),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).
	

%----------- if_acmpne ------------------------------
branch_instr('if_acmpne', state([EE|EEs],CT), Out, state([PosEE,NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1,_O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    jpl_call(InstrHandle,getTarget,[],NextHandle),
	jpl_call(NextHandle,getInstruction,[],NextInstr),
	jpl_call(NextInstr,getName,[],NextName),
    format(Out,'Branch on ~w~n',[IHToString]),
    writeln(Out,'True if_acmpne branch'),
    write(Out,'For if_acmpne Ive added the Positive Execution Environment'),
	write(NextName),
    PosEE = env(C, M, OS1, LVs, NextHandle),
    EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1,_O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format(Out,'Branch on ~w~n',[IHToString]),
	writeln(Out,'False if_acmpne branch'),	
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	write(Out,'For if_acmpne Ive added the Negative Execution Environment'),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).
	



branch_instr('if_acmpne', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1,_O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
%	format('False if_acmpne branch, [O1,O2] = [~w,~w]~n',[O1,O2]),
	CT = (CAssoc,CCW,VarPairs),
	unpack_sync(CCW, VarPairs, CW),
    FW=CW,
%    update_worldlist((O1=\=O2),CW,FW),
	pack_sync(FW,VarPairs,CFW),
	NewCT = (CAssoc,CFW,VarPairs),
	check_all_constraints(FW),
    get_next_instr(C,M,InstrHandle,false,NegInstrHandle),
%	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).




% -------------------------------------------------------





%------------ Kshitij G. Edited for Branch
branch_instr(ifnull, state([EE|EEs],CT),Out, state([PosEE,NegEE|EEs],NewCT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    jpl_call(InstrHandle,getTarget,[],PosInstrHandle),
	write(Out,'Positive Instruction handle for ifull added~n'),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle),
	(OS = [O1|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    jpl_call(InstrHandle,getNext,[],NegInstrHandle),
    write(Out,'Negative Instruction handle for ifull added~n'),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).

    
%------------ ifge------------------------------------

branch_instr(ifge, state([EE|EEs],CT), Out, state([PosEE,NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    jpl_call(InstrHandle,toString,[],String_InstrHandle),
    format(Out,'String of InstrHandle is:~n~w',[String_InstrHandle]),
    jpl_call(InstrHandle,getTarget,[],PosInstrHandle),
    write(Out,'Positive Instruction Handle for ifge added~n..'),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle),
	(OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    jpl_call(InstrHandle,getNext,[],NegInstrHandle),
    write(Out,'Negative Instruction handle for ifge added~n'),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).



branch_instr(goto, state([EE|EEs],CT), Out,state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    %jpl_call(InstrHandle, getTarget, [], BranchInstrHandle),
    jpl_call('mcparser.instr.InstructionInfo', getBranchTarget, [InstrHandle], BranchInstrHandle),
    (BranchInstrHandle \== @null ->
        jpl_call(BranchInstrHandle,getPosition,[],Offset),
        format('Offset is:',[Offset]),
        format('Goto offset ~w~n',[Offset]) ; true),
    
    jpl_call(InstrHandle,getPosition,[],PositionInstrHandle),
    %format(Out,'Next Instr Handle is:~w~n',[PositionInstrHandle]),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
    (Offset < PositionInstrHandle -> write(Out,'Skipping back looping!..'),write('Skipping back loop...'),NewEE = env(C, M, OS, LVs, NewInstrHandle);NewEE = env(C, M, OS, LVs, BranchInstrHandle)).

	



	%% (BranchInstrHandle \== @null ->
	%% 	jpl_call(InstrHandle,getPosition,[],PositionInstrHandle),
	%% 	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	%% 	format(Out,'Position of Instruction Handle is:~w~n',[PositionInstrHandle]),
 %%        jpl_call(BranchInstrHandle,getPosition,[],Offset),
 %%        format(Out,'Goto Offset is:~w~n',[Offset]),
 %%        atom_number(PositionInstrHandle,Int_PIH)
 %%        ((Offset > Int_PIH) -> format(Out,'Valid Goto Statement. Forward Jump~n'),
 %%        	format(Out,'Goto offset ~w~n',[Offset]),NewEE = env(C, M, [], LVs, BranchInstrHandle) ;
 %%        	write('Invalid goto~n'),format(Out,'Invalid Goto Statement...Not processing.~n'),
 %%        	NewEE = env(C, M, OS, LVs, NextInstrHandle)); true).
      
	

%------------ Kshitij G. Edited for Branch
branch_instr(if_icmpeq, state([EE|EEs],CT),Out, state([PosEE,NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format(Out,'Branch on ~w~n',[IHToString]),
	format(Out,'True if_icmpeq branch, [O1,O2] = [~w,~w]~n',[O1,O2]),
    jpl_call(InstrHandle,getTarget,[],PosInstrHandle),	
	PosEE = env(C, M, OS1, LVs, PosInstrHandle),
	write(Out,'For if_icmpeq Ive added the Positive Execution Environment'),
	(OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	format(Out,'False if_icmpeq branch, [O1,O2] = [~w,~w]~n',[O1,O2]),
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle),
	write(Out,'For if_icmpeq Ive added the Negative Execution Environment').


	
% ------------ if_icmpeg
branch_instr('if_icmpge', state([EE|EEs],CT),Out, state([PosEE,NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    writeln('True if_icmpge branch'),
    jpl_call(InstrHandle,getTarget,[],PosInstrHandle),	
	PosEE = env(C, M, OS1, LVs, PosInstrHandle),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	format(Out,'False if_icmpeq branch, [O1,O2] = [~w,~w]~n',[O1,O2]),
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).




call_idivision(state([EE|EEs],CT),Out,state([NewEE|EEs],CT)) :-
EE = env(C,M,OS,LVs,InstrHandle),
(OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
Result1 = O2 - O1,
((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
jpl_call(InstrHandle,getNext,[],NewInstrHandle),
NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).


call_constlongload(state([EE|EEs],CT), Out,state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getValue, [], Value),
	jpl_call(Value, longValue, [], LongValue),
	NewOS = [LongValue|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).


call_constldcload(state([EE|EEs],CT),Out, state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getLDCConstant, [C, InstrHandle], ConstantObject),
	(jpl_is_ref(ConstantObject) ->
        jpl_call('mcparser.instr.InstructionInfo',getNumericType,[ConstantObject],ObjectClassString),
        (ObjectClassString == 'Integer' ->
            jpl_call(ConstantObject,intValue,[],Constant)
            ;
            (ObjectClassString == 'Double' ->
                jpl_call(ConstantObject,doubleValue,[],Constant)
                ;
                (ObjectClassString == 'Long' ->
                    jpl_call(ConstantObject,longValue,[],Constant)
                    ;
                    (ObjectClassString == 'Float' ->
                        jpl_call(ConstantObject,floatValue,[],Constant)
                        ;
                        (ObjectClassString == 'Short' ->
                            jpl_call(ConstantObject,shortValue,[],Constant)
                            ;
                            (ObjectClassString == 'Byte' ->
                                jpl_call(ConstantObject,byteValue,[],Constant)
                                ;
                                jpl_call(ConstantObject,toString,[],Constant)))))))
        ;
		Constant = ConstantObject),
	NewOS = [Constant|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).

call_getfield(state([EE|EEs],CT),Out, state([NewEE|EEs],CT)) :-
	%objectref → value	get a field value of an object objectref, where the field is identified by field reference in the constant pool 
	%% EE = env(C,M,OS,LVs,InstrHandle),
	%% write(Out,'Processing putfield Instruction......'),
	%% jpl_call(InstrHandle, getInstruction,[], Instruction),
	%% jpl_call(C,getConstantPool,[], ConstantPoolGen),
	%% jpl_call(ConstantPoolGen,getConstantPool,[],ConstantPool),
	%% jpl_call(Instruction,getFieldName, [ConstantPoolGen],FieldName),
	%% format(Out,'Field is: ~w~n', FieldName),
	%% NewOS = [FieldName|OS],
	%% jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	%% jpl_call(NextInstrHandle,getInstruction,[], NextInstruction),
	%% jpl_call(NextInstruction,getName,[],InstructionName),
	%% format(Out,'NextInstruction is:~w~n',InstructionName),
	%% NewEE = env(C,M,NewOS,LVs,NextInstrHandle).
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1|OS1];(OS = [],OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [_FieldValue|OS1], LVs, NewInstrHandle).

call_ldcload(state([EE|EEs],CT),Out,state([NewEE|EEs],CT)) :-
%LDC : push a constant #index from a constant pool. eg: pushing "Hello World" onto the stack
EE = env(C,M,OS,LVs,InstrHandle),
jpl_call(InstrHandle, getInstruction,[], Instruction),
jpl_call(Instruction, getIndex,[],ReferencedIndex),
jpl_call(C,getConstantPool,[], ConstantPoolGen),
jpl_call(ConstantPoolGen,getConstantPool,[],ConstantPool),
jpl_call(ConstantPool,getConstant,[ReferencedIndex],ConstantFromPool),
jpl_call(ConstantFromPool, getStringIndex,[],StringIndex),
format(Out,'String index retrieved is: ~w~n',StringIndex),
%AFter getting the string index, retrieve the string from the constant pool
jpl_call(ConstantPool, getConstant,[StringIndex],Final_String),
jpl_call(Final_String,toString,[],String_FinalString),
format(Out,'String constant retrieved is: ~w~n',String_FinalString),
%Push Final_String onto the stack.
NewOS = [Final_String|OS],
jpl_call(InstrHandle,getNext,[],NewInstrHandle),
NewEE = env(C,M,NewOS,LVs,NewInstrHandle).




call_putfield(state([EE|EEs],CT),Out,state([NewEE|EEs],CT)) :-
%% %objectref, value →	set field to value in an object objectref, where the field is identified by a field reference index in constant pool 
%% write(Out,'Processing put Instruction'),
%% EE = env(C,M,OS,LVs,InstrHandle),
%% jpl_call(InstrHandle, getNext,[], NextInstrHandle),
%% OS = [Value,ObjectReference|RemOS],
%% jpl_call(InstrHandle,getNext,[],NewInstrHandle),
%% NewEE = env(C,M,RemOS,LVs,NewInstrHandle).
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	jpl_call('mcparser.instr.InstructionInfo', getFieldOpDataLite, [C, M, InstrHandle], FieldOpData),
	% jpl_get(FieldOpData, fieldType, FieldType),
	jpl_get(FieldOpData, fieldName, FieldName),
	jpl_get(FieldOpData, objType, ObjType),
	
	jpl_call(ObjType,toString,[],ObjTypeString),
	jpl_new('java.lang.StringBuilder',[ObjTypeString],NameStringBuilder),
	jpl_call(NameStringBuilder,append,['.'],_),
	jpl_call(NameStringBuilder,append,[FieldName],_),
	jpl_call(NameStringBuilder,toString,[],_FinalString),
    format('In putfield, pointer = ~w~nO1 = ~w~n', [O2, O1]),

    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle).




call_getstatic(state([EE|EEs],CT),Out,state([NewEE|EEs],CT)) :-
%% 	%puts the static field onto the stack identified by the index. 
%% 	EE = env(C,M,OS,LVs,InstrHandle),
%% 	%use Instruction Handle to getInstruction and then call getIndex to get the index referenced in the ConstantPool.
%% 	jpl_call(InstrHandle, getInstruction,[], Instruction),
%% 	jpl_call(Instruction, getIndex,[],ReferencedIndex),
%% %	format('ReferencedIndex in ConstantPool is: ~w~n',ReferencedIndex),
%% 	jpl_call(C,getConstantPool,[],ConstantPoolGen),
%% 	jpl_call(ConstantPoolGen,getConstantPool,[],ConstantPool),
%% 	%Call getConstant which returns an object of type Constant.
%% 	jpl_call(ConstantPool, getConstant,[ReferencedIndex], ConstantFromPool),
%% 	% Push this value on the stack.....
%% 	NewOS = [ConstantFromPool|OS],
%% 	jpl_call(InstrHandle,getNext,[], NewInstrHandle),
%% 	NewEE = env(C,M,NewOS,LVs,NewInstrHandle).
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getFieldOpDataLite, [C, M, InstrHandle], FieldOpData),
	% jpl_get(FieldOpData, fieldType, FieldType),
    jpl_get(FieldOpData,className,ClassName),
	jpl_get(FieldOpData, fieldName, FieldName),
	
	jpl_get(FieldOpData, objType, ObjType),

	jpl_call(ObjType,toString,[],ObjTypeString),
	jpl_new('java.lang.StringBuilder',[ObjTypeString],NameStringBuilder),
	jpl_call(NameStringBuilder,append,['.'],_),
	jpl_call(NameStringBuilder,append,[FieldName],_),
	jpl_call(NameStringBuilder,toString,[],FinalString),
	
	format('In getstatic, FinalString = ~w~n', FinalString),
	format('FieldName is, NewOS is ~w~w~n', [FieldName, NewOS]),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).
call_constintload(state([EE|EEs],CT),Out, state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getValue, [], Value),
	jpl_call(Value, intValue, [], IntValue),
	NewOS = [IntValue|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).

call_localload(state([EE|EEs],CT), Out,state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call('mcparser.instr.InstructionInfo', getLocalVariableIndex, [InstrHandle], Index),
	format(Out,'in localload, Index is ~w~n', Index),
    get_assoc(Index, LVs, Value),
	NewOS = [Value|OS],					%get the local variable from the Association List and Push it on the OperandStack.
	%jpl_call(Value, toString,[],String_Value),
	%format('String representation of value is: ~w~n',String_Value),		FYI this is LocalVariableGen(this,Kshitij,0:aload_0[42](1),4:return[177](1)) i.e name,type,start,end
	format(Out,'Value is ~w~n, LVs is ~w~n, NewOS is ~w~n',[Value, LVs, NewOS]),
	jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).

call_localstore(state([EE|EEs],CT),Out, state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call('mcparser.instr.InstructionInfo', getLocalVariableIndex, [InstrHandle], Index),
	(OS = [Value|OS1] ; (OS = [], OS1 = [])),
    put_assoc(Index, LVs, Value, NewLVs),
	format(Out,'In localstore OS:~w~n Index:~w~n NewLVs:~w~n',[OS,Index,NewLVs]),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, NewLVs, NewInstrHandle).
increment(X, X1):-
	X1 is X+1.