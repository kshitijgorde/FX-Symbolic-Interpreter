:-['utility'].
:-['callgraph'].
:-['classlist'].
:- use_module(library(assoc)).

process_classes([]).
process_classes([C|CList]) :-
	jpl_call('mcparser.instr.InstructionInfo',getClassGen,[C],CGen),		%Cgen is a datastructure from bcel that holds class related info.
	format('The ClassGen is: ~w~n',CGen),
	%jpl_call('mcparser.instr.InstructionInfo',getClassMethods,[CGen],MArrayList),
    %arraylist_to_list(MArrayList,MList),
	jpl_call('mcparser.ClassParser',createMethodGenArray,[CGen],CMethodGenArray), %returns method array which returns all methods in the given CGen.
	format('The MethodGenArray retrieved is: ~w~n',CMethodGenArray),
	jpl_array_to_list(CMethodGenArray,[First,MGen1|MGenList]),
	writeln([First,MGen1|MGenList]),
	
	write('\n\n'),
	jpl_call(MGen1,getMethod,[],Method1),	%MethodGen is not the same as Method (Both are differnce data structures)	..this will be public void init...
	jpl_call(Method1,getName,[],Naam1),
	jpl_call(Method1,getSignature,[],Sig1),
	atom_concat(Naam1,Sig1,Trial1),
	format('Method name:~w~n',Naam1),
	format('Its signature is:~w~n',Sig1),	
	format('MethodGen1 ~s~n',[Trial1]),
	%jpl_call(MGen2,getMethod,[],Method2),
	%jpl_call(Method2,getName,[],Naam),
	%jpl_call(Method2,getSignature,[],Sig),
	%atom_concat(Naam,Sig,Trial),
	%format('MethodGen2 ~s~n~n',[Trial]),
	jpl_call(MGen1,getInstructionList,[],MIList),
	jpl_call(MIList,toString,[],String_MIList),
	format('The Instruction List is: ~w~n',String_MIList),
	jpl_call(MIList,getInstructionHandles,[],IHArray),
	jpl_array_to_list(IHArray,[IH|InstructionHandleList]),
	
	jpl_call(MGen1,getLocalVariables,[],LVArray),	%LVArray is a LocalVariableGen[] from bcel library
   	%format('LocalVariable Gen is ~w~n',LVArray),
    jpl_array_to_list(LVArray, LVList),
    list_to_indexed_assoc(LVList, LocalVars),
    format('Local Variables:~w~n',LocalVars),		% This representation is of the AVL Tree form. See documentation for more.
	OperandStack = [],
	%jpl_call(MGen2,getLocalVariables,[],MLVArray),
    %jpl_array_to_list(MLVArray, MLVList),
    %list_to_indexed_assoc(MLVList, MLocalVars),
	%write(MLocalVars),
	S = state([env(CGen,MGen1,OperandStack,LocalVars,IH)],[]),	%The first instruction handle will give you the next one. Hence only the first required
	instr(S,NewState).
	%process_methods_in_class(MGenList).
	%process_classes(CList).
	
instr(state([EE|_EEs],CTriple), NewState) :-
    % Stop if we're at a null instruction handle
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	InstrHandle == @null,
	write('Yesssssssssssssssssss!'),
	NewState = state([],CTriple).
instr(state([EE|EEs],CTriple), NewState) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	InstrHandle \== @null,
	jpl_call(C,getClassName,[],CToString),		% returns a string with class name\

	jpl_call(M,getName,[],MToString),	
	jpl_call(M,getSignature,[],MSigToString),
    atom_concat(MToString,MSigToString,MFullSig),
    atom_concat(CToString,'.',FullMethodName1),
    atom_concat(FullMethodName1,MFullSig,FullMethodName), %FullMethodName example is:	Kshitij.<init>()V
    format('Full method name is ~w~n',FullMethodName),		
    jpl_call(InstrHandle,getPosition,[],InstrOffset),
   	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getName, [], Label),
	jpl_call(Instr,toString,[],StringInstr),	
	jpl_call('mcparser.instr.InstructionInfo', getInstrType, [InstrHandle], InstrType),
    
    jpl_call(InstrHandle,toString,[@false],IHToString),
	format('OS=~w,LVs=~w,InstrHandle=~s~n~n, Type ~w~n',[OS,LVs,IHToString,InstrType]),
    help_instr(InstrType,state([EE|EEs],CTriple),NextState),
    instr(NextState,NewState).
    


help_instr(default, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call(InstrHandle,toString,[],IHToString),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    default_instr(Label, state([EE|EEs],CT), State2).

help_instr(get,state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    get_instr(Label, state([EE|EEs],CT), State2).	 
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
	format('Label from return help_instr:~w~n',Label),
    return_instr(Label, state([EE|EEs],CT), State2).

help_instr(put,state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	put_instr(Label, state([EE|EEs],CT), State2).


help_instr(invoke, state([EE|EEs],CT), state(ReturnEEs, CT)) :-
% This help_instr is for trusted classes. In case of trusted classes we do not need NewMethodEE

%\+(cat(X)) is the same as not(cat(X))
EE = env(C,M,OS, LVs, InstrHandle),




jpl_call('mcparser.instr.InstructionInfo', getInvokeDataLite, [C,M,InstrHandle], InvokeData),
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

format('Updated OperandStack:~w~n',[UpdatedOS]),	
format('Processing Trusted Classes for Invoke Instruction'),

writeln('invoke, trusted case'),
format('ClassName = ~w~n', NewClassName),
format('MethodName = ~w~n', [MethodName]),
% This is a trusted class...No we need not invoke it's method. Just populate ReturnEE as the next state.
jpl_call(InstrHandle,getNext,[],NextInstructionHandle),
ReturnEE = env(C,M,UpdatedOS,LVs,NextInstructionHandle),
ReturnEEs = [ReturnEE|EEs].



help_instr(invoke, state([EE|EEs],CT), state([NewMethodEE, ReturnEE|EEs],NewCT)) :-
% This help_instr is for non-trusted classes. In case of Untrusted classes we need NewMethodEE

%\+(cat(X)) is the same as not(cat(X))
EE = env(C,M,OS, LVs, InstrHandle),
jpl_call('mcparser.instr.InstructionInfo', getInvokeData, [C,M,InstrHandle], InvokeData),	
jpl_call(InstrHandle, getInstruction, [], Instr),
jpl_call(Instr, getName, [], Label),
format('In untrusted: OS:~w~n',[OS]),
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
%NOneed to update OS here in untrusted classes.
	
jpl_get(InvokeData, className, NewClassName),
\+trusted_class(NewClassName),					%match with trusted_class should fail.
format('Processing UnTrusted Classes for Invoke Instruction~n'),
format('ClassName = ~w~n', NewClassName),
format('MethodName = ~w~n', [MethodName]),
jpl_call(InstrHandle,getNext,[],NextInstructionHandle),
ReturnEE = env(C,M,NewOS,LVs,NextInstructionHandle),

%To populate a NewMethodEE, get new LocalVars, convert to prolog list, and index assoc.
jpl_get(InvokeData, cgen, NewClassGen),
jpl_get(InvokeData, mgen, NewMethodGen),
jpl_call(NewMethodGen,getLocalVariables,[],LVArray),
jpl_array_to_list(LVArray, LVList),
list_to_indexed_assoc(LVList, NewLocalVars),
jpl_call(NewMethodGen,getInstructionList,[],NewMethodGenInstrutionList),
jpl_call(NewMethodGenInstrutionList,toString,[],String_MIList),
format('The Instruction List is: ~w~n',String_MIList),
jpl_call(NewMethodGenInstrutionList,getInstructionHandles,[],IHArray),
jpl_array_to_list(IHArray,[IH|InstructionHandleList]),
NewMethodEE = env(NewClassGen, NewMethodGen, [], NewLocalVars, IH),
format('Added new Untrusted Method to the list of Execution Environments.').







print_instructions_from_handles([]).
print_instructions_from_handles([IH|InstructionHandleList]) :-
	jpl_call(IH,getInstruction,[],Instr),
	jpl_call(Instr,getName,[],Name),
	writeln(Name),
	print_instructions_from_handles(InstructionHandleList).

typed_instr(idiv, State1, State2) :- call_idivision(State1, State2).
typed_instr(iconst_0, State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_5, State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_3, State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_2,State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_1,State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_m1,State1,State2) :- call_constintload(State1,State2).
typed_instr(lconst_0,State1,State2) :- call_constlongload(State1,State2).
typed_instr(ldc, State1, State2) :- call_constldcload(State1, State2).
typed_instr(sipush, State1, State2) :- call_constintload(State1, State2).
local_instr(istore,State1,State2) :- call_localstore(State1,State2).
local_instr(istore_0, State1, State2) :- call_localstore(State1, State2).
local_instr(istore_1, State1, State2) :- call_localstore(State1, State2).
local_instr(istore_2, State1, State2) :- call_localstore(State1, State2).
local_instr(istore_3, State1, State2) :- call_localstore(State1, State2).
local_instr(lstore,State1, State2) :- call_localstore(State1, State2).
local_instr(iload_2, State1, State2) :- call_localload(State1, State2).
local_instr(iload_0, State1, State2) :- call_localload(State1, State2).
local_instr(iload_3, State1, State2) :- call_localload(State1, State2).
local_instr(iload_1, State1, State2) :- call_localload(State1, State2).
local_instr(aload,State1,State2) :- call_localload(State1,State2).
local_instr(aload_0, State1, State2) :- call_localload(State1, State2).
local_instr(aload_1, State1, State2) :- call_localload(State1, State2).
local_instr(aload_2, State1, State2) :- call_localload(State1, State2).
local_instr(aload_3, State1, State2) :- call_localload(State1, State2).
local_instr(astore_1, State1, State2) :- call_localstore(State1, State2).
local_instr(astore_2, State1, State2) :- call_localstore(State1, State2).
local_instr(astore_3, State1, State2) :- call_localstore(State1, State2).
local_instr(astore_4, State1, State2) :- call_localstore(State1, State2).
local_instr(astore, State1, State2) :- call_localstore(State1, State2).
get_instr(getstatic, State1, State2) :- call_getstatic(State1, State2).
get_instr(getfield, State1, State2) :- call_getfield(State1, State2).
put_instr(putfield, State1, State2) :- call_putfield(State1, State2).
% In case of normal returns, simply pop the callee execution env
return_instr(return, state([_CalleeEE,CallerEE|EEs],CT), state([NewCallerEE|EEs],CT)) :-
	writeln('coming to first return case'),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
%    get_next_instr(OldC,OldM,OldInstrHandle,NextInstrHandle),
	NewCallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
	jpl_call(OldC,toString,[],String_OldC),
	format('Old C is ~w~n',String_OldC),
	jpl_call(OldM,toString,[],String_OldM),
	format('Old M is ~w~n',String_OldM),
	jpl_call(OldInstrHandle,toString,[],String_OldInstrHandle),
	format('Old Instr Handle is ~w~n',String_OldInstrHandle).

% A return WITHOUT an underlying method
return_instr(_, state([_OldEE],CT), state([FinalEE],CT)) :-
    FinalEE = env(c,m,os,lvs,@null), % setting the next instruction to null means we're at the end
	writeln('bottom-level return').

return_instr(areturn, state([CalleeEE,CallerEE|EEs],CT), state( [NewCallerEE|EEs],CT)) :-
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


return_instr(ireturn, state([CalleeEE,CallerEE|EEs],CT), state( [NewCallerEE|EEs],CT)) :-
	CalleeEE = env(_C, _M, CalleeOS, _LVs, _InstrHandle),
    (CalleeOS = [RetVar|_] ; CalleeOS = []),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
%    get_next_instr(OldC,OldM,OldInstrHandle,NextInstrHandle),
	NewCallerEE = env(OldC, OldM, [RetVar|OldOS], OldLVs, OldInstrHandle).


typed_instr(aastore,state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	format('Processing aastore........'),
	EE = env(C,M,OS,LVs,InstrHandle),
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	NewEE = env(C,M,OS,LVs,NextInstrHandle).



typed_instr(aconst_null, state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	% Push a null reference onto the stack
	EE = env(C,M,OS,LVs,InstrHandle),
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	NewOS = [null|OS],
	NewEE = env(C,M,NewOS,LVs, NextInstrHandle),
	format('In aconst_null, NewEE is :NewOS=~w , NextInstrHandle = ~w',[NewOS,NextInstrHandle]).


typed_instr(anewarray,state([EE|EEs],CT), state([NewEE,EEs],CT)) :-
	EE = env(C,M,OS,LVs,InstrHandle),
	OS = [OS1|RemOS],
	format('In anewarray OS:~w~n',[RemOS]),
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	jpl_call(NextInstrHandle,getInstruction,[],Instruction),
	jpl_call(Instruction,toString,[],String_Instruction),
	format('Next Instruction is: ~w~n',String_Instruction),
	NewEE = env(C,M,RemOS,LVs,NextInstrHandle).


typed_instr(new, state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getTypedParam, [C, InstrHandle], Type),
	jpl_call(Type,toString,[],String_Type),
	format('The Type retrieved is: ~w~n',String_Type),
	jpl_call('mcparser.instr.InstructionInfo', getClassFromType, [Type], RelevantClassGen),
    (RelevantClassGen \== @null ->
        jpl_call(RelevantClassGen, getClassName, [], ClassName)
        ;
        writeln('Could not obtain class definition'),
        ClassName = '?'),
    NewOS = [classname(ClassName)|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).


typed_instr(isub, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	Result1 = O2 - O1,
    ((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).

default_instr(newarray, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
	format('Processing newarray Instruction~n'),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_ArrayLength|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, ['array_primitive'|OS1], LVs, NewInstrHandle).
default_instr(dup, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
	%Duplicates the value on top of the stack....
	format('Processing dup instruction..'),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [O1,O1|OS1], LVs, NewInstrHandle).


default_instr(pop, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1|OS1] ; (OS = [] ; OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle).
%-------------- For branch instruction you have to take 2 branches. Condition Positive and Condition Negative

branch_instr('iflt', state([EE|EEs],CT), state([PosEE,NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
%	format('True iflt branch, [O] = [~w]~n',[O]),
	jpl_call(InstrHandle, getTarget,[],PosInstrHandle),
	jpl_call(PosInstrHandle,toString,[],Target_String),
	format('Target is:~w~n',[Target_String]),
	format('Positive EE added........~n'),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle),
	jpl_call(InstrHandle, getNext,[],NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle),
	format('Negative EE EE added........').

%------------------------- Now Handle for Neg. Instruction ---------------------------------------
branch_instr('iflt', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	jpl_call(InstrHandle, getNext,[],NegInstrHandle),
	jpl_call(NegInstrHandle,toString,[],NextTarget_String),
	format('Next Target is:~w~n',[NextTarget_String]).
		
	



%-------------------------------------------------------------------------------------------------



branch_instr('if_icmple', state([EE|EEs],CT), state([PosEE|EEs],NewCT)):-
	writeln('true'),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
	jpl_call(InstrHandle,getTarget,[],NextHandle),
	jpl_call(NextHandle,getInstruction,[],NextInstr),
	jpl_call(NextInstr,getName,[],NextName),
    format('Branch on ~w~n',[IHToString]),
    writeln('True if_icmple branch'),
	write(NextName),
    PosEE = env(C, M, OS1, LVs, NextHandle).
	
branch_instr('if_icmple', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	writeln('false'),
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	writeln('False if_icmple branch'),	
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).

branch_instr('goto', state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle, getTarget, [], BranchInstrHandle),
	(BranchInstrHandle \== @null ->
        jpl_call(BranchInstrHandle,getPosition,[],Offset),
        format('Goto offset ~w~n',[Offset]) ; true),
	NewEE = env(C, M, [], LVs, BranchInstrHandle).



call_idivision(state([EE|EEs],CT),state([NewEE|EEs],CT)) :-
EE = env(C,M,OS,LVs,InstrHandle),
(OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
Result1 = O2 - O1,
((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
jpl_call(InstrHandle,getNext,[],NewInstrHandle),
NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).


call_constlongload(state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getValue, [], Value),
	jpl_call(Value, longValue, [], LongValue),
	NewOS = [LongValue|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).


call_constldcload(state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
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

call_getfield(state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	%objectref → value	get a field value of an object objectref, where the field is identified by field reference in the constant pool 
	EE = env(C,M,OS,LVs,InstrHandle),
	format('Processing putfield Instruction......'),
	jpl_call(InstrHandle, getInstruction,[], Instruction),
	jpl_call(C,getConstantPool,[], ConstantPoolGen),
	jpl_call(ConstantPoolGen,getConstantPool,[],ConstantPool),
	jpl_call(Instruction,getFieldName, [ConstantPoolGen],FieldName),
	format('Field is: ~w~n', FieldName),
	NewOS = [FieldName|OS],
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	jpl_call(NextInstrHandle,getInstruction,[], NextInstruction),
	jpl_call(NextInstruction,getName,[],InstructionName),
	format('NextInstruction is:~w~n',InstructionName),
	NewEE = env(C,M,NewOS,LVs,NextInstrHandle).

call_ldcload(state([EE|EEs],CT),state([NewEE|EEs],CT)) :-
%LDC : push a constant #index from a constant pool. eg: pushing "Hello World" onto the stack
EE = env(C,M,OS,LVs,InstrHandle),
jpl_call(InstrHandle, getInstruction,[], Instruction),
jpl_call(Instruction, getIndex,[],ReferencedIndex),
jpl_call(C,getConstantPool,[], ConstantPoolGen),
jpl_call(ConstantPoolGen,getConstantPool,[],ConstantPool),
jpl_call(ConstantPool,getConstant,[ReferencedIndex],ConstantFromPool),
jpl_call(ConstantFromPool, getStringIndex,[],StringIndex),
format('String index retrieved is: ~w~n',StringIndex),
%AFter getting the string index, retrieve the string from the constant pool
jpl_call(ConstantPool, getConstant,[StringIndex],Final_String),
jpl_call(Final_String,toString,[],String_FinalString),
format('String constant retrieved is: ~w~n',String_FinalString),
%Push Final_String onto the stack.
NewOS = [Final_String|OS],
jpl_call(InstrHandle,getNext,[],NewInstrHandle),
NewEE = env(C,M,NewOS,LVs,NewInstrHandle).




call_putfield(state([EE|EEs],CT),state([NewEE|EEs],CT)) :-
%objectref, value →	set field to value in an object objectref, where the field is identified by a field reference index in constant pool 
format('Processing put Instruction'),
EE = env(C,M,OS,LVs,InstrHandle),
jpl_call(InstrHandle, getNext,[], NextInstrHandle),
OS = [Value,ObjectReference|RemOS],
jpl_call(InstrHandle,getNext,[],NewInstrHandle),
NewEE = env(C,M,RemOS,LVs,NewInstrHandle).




call_getstatic(state([EE|EEs],CT),state([NewEE|EEs],CT)) :-
	%puts the static field onto the stack identified by the index. 
	EE = env(C,M,OS,LVs,InstrHandle),
	%use Instruction Handle to getInstruction and then call getIndex to get the index referenced in the ConstantPool.
	jpl_call(InstrHandle, getInstruction,[], Instruction),
	jpl_call(Instruction, getIndex,[],ReferencedIndex),
%	format('ReferencedIndex in ConstantPool is: ~w~n',ReferencedIndex),
	jpl_call(C,getConstantPool,[],ConstantPoolGen),
	jpl_call(ConstantPoolGen,getConstantPool,[],ConstantPool),
	%Call getConstant which returns an object of type Constant.
	jpl_call(ConstantPool, getConstant,[ReferencedIndex], ConstantFromPool),
	% Push this value on the stack.....
	NewOS = [ConstantFromPool|OS],
	jpl_call(InstrHandle,getNext,[], NewInstrHandle),
	NewEE = env(C,M,NewOS,LVs,NewInstrHandle).
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
    jpl_call('mcparser.instr.InstructionInfo', getLocalVariableIndex, [InstrHandle], Index),
	format('in localload, Index is ~w~n', Index),
    get_assoc(Index, LVs, Value),
	NewOS = [Value|OS],					%get the local variable from the Association List and Push it on the OperandStack.
	%jpl_call(Value, toString,[],String_Value),
	%format('String representation of value is: ~w~n',String_Value),		FYI this is LocalVariableGen(this,Kshitij,0:aload_0[42](1),4:return[177](1)) i.e name,type,start,end
	format('Value is ~w~n, LVs is ~w~n, NewOS is ~w~n',[Value, LVs, NewOS]),
	jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).

call_localstore(state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call('mcparser.instr.InstructionInfo', getLocalVariableIndex, [InstrHandle], Index),
	(OS = [Value|OS1] ; (OS = [], OS1 = [])),
    put_assoc(Index, LVs, Value, NewLVs),
	format('In localstore OS:~w~n Index:~w~n NewLVs:~w~n',[OS,Index,NewLVs]),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, NewLVs, NewInstrHandle).
increment(X, X1):-
	X1 is X+1.