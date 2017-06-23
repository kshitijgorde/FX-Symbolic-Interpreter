:-['utility'].
:-['callgraph'].
:-[classlist].
:- use_module(library(assoc)).


process_classes([]).
process_classes([C|CList]) :-
	write("In Process Classes..."),
	jpl_call('mcparser.instr.InstructionInfo',getClassGen,[C],CGen),
	write(CGen),
	write("\n"),
	%jpl_call('mcparser.instr.InstructionInfo',getClassMethods,[CGen],MArrayList),
    %arraylist_to_list(MArrayList,MList),
	jpl_call('mcparser.ClassParser',createMethodGenArray,[CGen],CMethodGenArray),
	write(CMethodGenArray),
	write("\n"),
	jpl_array_to_list(CMethodGenArray,[MGen1|MGenList]),
	writeln([MGen1|MGenList]),
	write('\n\n'),
	jpl_call(MGen1,getMethod,[],Method1),
	jpl_call(Method1,getName,[],Naam1),
	jpl_call(Method1,getSignature,[],Sig1),
	atom_concat(Naam1,Sig1,Trial1),
	format('MethodGen1 ~s~n',[Trial1]),
	jpl_call(MGen1,getInstructionList,[],MIList),
	jpl_call(MIList,getInstructionHandles,[],IHArray),
	jpl_array_to_list(IHArray,[IH|InstructionHandleList]),
	
	jpl_call(MGen1,getLocalVariables,[],LVArray),
    jpl_array_to_list(LVArray, LVList),
    list_to_indexed_assoc(LVList, LocalVars),
	OperandStack = [],
	S = state([env(CGen,MGen1,OperandStack,LocalVars,IH)],[]),
	write(IH),
	instr(S,NewState).
	%process_methods_in_class(MGenList).
	%process_classes(CList).
	
instr(state([EE|_EEs],CTriple), NewState) :-
    % Stop if we are at a null instruction handle
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	InstrHandle == @null,
	%write('Yesssssssssssssssssss!'),
	NewState = state([],CTriple).
instr(state([EE|EEs],CTriple), NewState) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	InstrHandle \== @null,
	write(InstrHandle),
	jpl_call(C,getClassName,[],CToString),
	jpl_call(M,getName,[],MToString),	
	jpl_call(M,getSignature,[],MSigToString),
    atom_concat(MToString,MSigToString,MFullSig),
    atom_concat(CToString,'.',FullMethodName1),
    atom_concat(FullMethodName1,MFullSig,FullMethodName),
    jpl_call(InstrHandle,getPosition,[],InstrOffset),

	jpl_call(InstrHandle, getInstruction, [], Instr),
	jpl_call(Instr, getName, [], Label),
	
	jpl_call('mcparser.instr.InstructionInfo', getInstrType, [InstrHandle], InstrType),
    
    jpl_call(InstrHandle,toString,[@false],IHToString),
	%format('OS=~w,LVs=~w,InstrHandle=~s~n~n, Type ~w~n',[OS,LVs,IHToString,InstrType]),
    help_instr(InstrType,state([EE|EEs],CTriple),NextState),
    instr(NextState,NewState).
	 
help_instr(typed, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call(InstrHandle,toString,[@false],IHToString),
	write(IHToString),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    typed_instr(Label, state([EE|EEs],CT), State2).
help_instr(local, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call(InstrHandle,toString,[@false],IHToString),
	write(IHToString),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	local_instr(Label, state([EE|EEs],CT), State2).
help_instr(branch, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),    
	jpl_call(InstrHandle,toString,[@false],IHToString),
	write(IHToString),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    branch_instr(Label, state([EE|EEs],CT), State2).
help_instr(return, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),    
	jpl_call(InstrHandle,toString,[@false],IHToString),
	write(IHToString),
	jpl_call(InstrHandle,getInstruction,[],Instruction),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    return_instr(Label, state([EE|EEs],CT), State2).

help_instr(default, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call(InstrHandle,toString,[@false],IHToString),
	write(IHToString),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
    default_instr(Label, state([EE|EEs],CT), State2).
	
help_instr(put, state([EE|EEs],CT), State2) :-
	EE = env(_C, _M, _OS, _LVs, InstrHandle),
	jpl_call(InstrHandle,toString,[@false],IHToString),
	write(IHToString),
	jpl_call('mcparser.instr.InstructionInfo', getInstrName, [InstrHandle], Label),
	put_instr(Label, state([EE|EEs],CT), State2).

help_instr(invoke, state([EE|EEs],CT), state([NewMethodEE, ReturnEE|EEs],NewCT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call(InstrHandle,toString,[@false],IHToString),
	write(IHToString),
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
		jpl_call('mcparser.util.Misc',getMethodGen,[JavaClass,'init()V'],NewMethodGen);NewMethodGen = MGEn),
	
    jpl_call(NewMethodGen,getInstructionList, [], NewInstructionList),
	jpl_call(NewInstructionList,getInstructionHandles,[],NewMethodInstrHandleArray),
    jpl_array_to_list(NewMethodInstrHandleArray,[NewMethodInstrHandle|NewMethodInstrHandleList]),
	
	jpl_call(Instr, getName, [], Label),

	jpl_call(Instr,getArgumentTypes,[ConstantPoolGen],ArgArray),
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
	
	jpl_call(InstrHandle,getNext,[],NextInstrHandle),
	jpl_call(NextInstrHandle,getInstruction,[],I),
	jpl_call(I,getName,[],L),
    ReturnEE = env(C, M, NewOS, LVs, NextInstrHandle),
	format('ReturnEE: OS=~w,LVs=~w,InstrHandle=~s~n~n',[NewOS,LVs,L]),

	jpl_call(NewMethodGen,getLocalVariables,[],NewLVArray),
	jpl_array_to_list(NewLVArray, NewLVList),
    list_to_indexed_assoc(NewLVList, NewLocalVars),
	
	length(NewLVList, LVlength),
	format('LVlength = ~w~nArgListLength = ~w~n', [LVlength,ArgListLength]),
	format('Label: ~w~n, N: ~w~n, NewLocalVars:~w~n',[Label,N,NewLocalVars]),
	
	NewMethodEE = env(C, NewMethodGen, [], NewLocalVars, NewMethodInstrHandle),
	jpl_call(NewMethodInstrHandle,getInstruction,[],NI),
	jpl_call(NI,getName,[],NL),
	format('NewMethodEE: OS=~w,LVs=~w,InstrHandle=~w~n~n',[[],NewLocalVars,NL]).
	
print_instructions_from_handles([]).
print_instructions_from_handles([IH|InstructionHandleList]) :-
	jpl_call(IH,getInstruction,[],Instr),
	jpl_call(Instr,getName,[],Name),
	writeln(Name),
	print_instructions_from_handles(InstructionHandleList).


typed_instr(iconst_0, State1, State2) :- call_constintload(State1, State2).
local_instr(istore_1, State1, State2) :- call_localstore(State1, State2).
typed_instr(iconst_5, State1, State2) :- call_constintload(State1, State2).
local_instr(istore_0, State1, State2) :- call_localstore(State1, State2).
local_instr(istore_2, State1, State2) :- call_localstore(State1, State2).
typed_instr(iconst_3, State1, State2) :- call_constintload(State1, State2).
local_instr(istore_3, State1, State2) :- call_localstore(State1, State2).
local_instr(iload_2, State1, State2) :- call_localload(State1, State2).
local_instr(iload_0, State1, State2) :- call_localload(State1, State2).
local_instr(iload_3, State1, State2) :- call_localload(State1, State2).
local_instr(iload_1, State1, State2) :- call_localload(State1, State2).
local_instr(aload,State1,State2) :- call_localload(State1,State2).
local_instr(aload_0, State1, State2) :- call_localload(State1, State2).
local_instr(aload_1, State1, State2) :- call_localload(State1, State2).
local_instr(aload_2, State1, State2) :- call_localload(State1, State2).
local_instr(aload_3, State1, State2) :- call_localload(State1, State2).
typed_instr(ldc, State1, State2) :- call_constldcload(State1, State2).
local_instr(astore_1, State1, State2) :- call_localstore(State1, State2).
typed_instr(bipush, State1, State2) :- call_constintload(State1,State2).
typed_instr(sipush, State1, State2) :- call_constintload(State1, State2).
local_instr(astore_2, State1, State2) :- call_localstore(State1, State2).
typed_instr(iconst_1, State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_2, State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_3, State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_4, State1, State2) :- call_constintload(State1, State2).
typed_instr(iconst_5, State1, State2) :- call_constintload(State1, State2).
local_instr(astore_3, State1, State2) :- call_localstore(State1, State2).
local_instr(istore,State1,State2) :- call_localstore(State1,State2).
local_instr(iload, State1, State2) :- call_localload(State1,State2).
local_instr(astore,State1,State2) :- call_localstore(State1,State2).

% In case of normal returns, simply pop the callee execution env
return_instr(return, state([_CalleeEE,CallerEE|EEs],CT), state([NewCallerEE|EEs],CT)) :-
	writeln('coming to first return case'),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
	NewCallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle).

% A return WITHOUT an underlying method
return_instr(_, state([_OldEE],CT), state([FinalEE],CT)) :-
    FinalEE = env(c,m,os,lvs,@null), % setting the next instruction to null means we're at the end
	writeln('bottom-level return').

typed_instr(isub, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
	Result1 = O2 - O1,
    ((number(O1),number(O2)) -> Result is Result1 ; Result = Result1),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [Result|OS1], LVs, NewInstrHandle).

typed_instr(new, state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getTypedParam, [C, InstrHandle], Type),
	format('The Type retrieved is: ~w~n',Type),
	jpl_call('mcparser.instr.InstructionInfo', getClassFromType, [Type], RelevantClassGen),
    (RelevantClassGen \== @null ->
        jpl_call(RelevantClassGen, getClassName, [], ClassName)
        ;
        writeln('Could not obtain class definition'),
        ClassName = '?'),
    NewOS = [classname(ClassName)|OS],
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).
	
typed_instr(iaload,state([EE|EEs],CT),state([NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
    EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_Int,_Index|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, ['array_value'|OS1], LVs, NewInstrHandle).
	
typed_instr(iastore,state([EE|EEs],CT),state([NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
    EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_Int,_Index,_Value|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle).
	
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

branch_instr('ifeq', state([EE|EEs],CT), state([PosEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	format('True ifeq branch, [O] = [~w]~n',[O]),
	jpl_call(InstrHandle,getTarget,[],PosInstrHandle),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle).

branch_instr('if_icmpge', state([EE|EEs],CT), state([PosEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    writeln('True if_icmpge branch'),
	jpl_call(InstrHandle,getTarget,[],PosInstrHandle),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle).

branch_instr('if_icmpge', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
    writeln('False if_icmpge branch'),
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).

branch_instr('if_icmplt', state([EE|EEs],CT), state([PosEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	format('True if_icmplt branch, [O1,O2] = [~w,~w]~n',[O1,O2]),

	jpl_call(InstrHandle,getTarget,[],PosInstrHandle),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle).

branch_instr('if_icmplt', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1,O2|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	format('False if_icmplt branch, [O1,O2] = [~w,~w]~n',[O1,O2]),
	 
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).

branch_instr('ifeq', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	format('False ifeq branch, [O] = [~w]~n',[O]),
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).
	
branch_instr('goto', state([EE|EEs],CT), state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle, getTarget, [], BranchInstrHandle),
	(BranchInstrHandle \== @null ->
        jpl_call(BranchInstrHandle,getPosition,[],Offset),
        format('Goto offset ~w~n',[Offset]) ; true),
	NewEE = env(C, M, [], LVs, BranchInstrHandle).
	
branch_instr('iflt', state([EE|EEs],CT), state([PosEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	jpl_call(InstrHandle,getTarget,[],PosInstrHandle),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle).

branch_instr('iflt', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).

branch_instr('ifge', state([EE|EEs],CT), state([PosEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	jpl_call(InstrHandle,getTarget,[],PosInstrHandle),
	PosEE = env(C, M, OS1, LVs, PosInstrHandle).

branch_instr('ifge', state([EE|EEs],CT), state([NegEE|EEs],NewCT)):-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,toString,[@false],IHToString),
    format('Branch on ~w~n',[IHToString]),
	jpl_call(InstrHandle, getNext, [], NegInstrHandle),
	NegEE = env(C, M, OS1, LVs, NegInstrHandle).

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
	NewOS = [Value|OS],
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

get_instr(getstatic, state([EE|EEs],CT), state([NewEE|EEs],NewCT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
	jpl_call('mcparser.instr.InstructionInfo', getFieldOpDataLite, [C, M, InstrHandle], FieldOpData),
	jpl_get(FieldOpData,className,ClassName),
	jpl_get(FieldOpData, fieldName, FieldName),
	
	jpl_get(FieldOpData, objType, ObjType),

	jpl_call(ObjType,toString,[],ObjTypeString),
	jpl_new('java.lang.StringBuilder',[ObjTypeString],NameStringBuilder),
	jpl_call(NameStringBuilder,append,['.'],_),
	jpl_call(NameStringBuilder,append,[FieldName],_),
	jpl_call(NameStringBuilder,toString,[],FinalString),
	
	format('In getstatic, FinalString = ~w~n', FinalString),
	NewOS = [_NewVar|OS],
	jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, NewOS, LVs, NewInstrHandle).
	
default_instr(dup, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, [O1,O1|OS1], LVs, NewInstrHandle).
	
default_instr(newarray, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
    % Currently we don't really reason about arrays...
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_ArrayLength|OS1] ; (OS = [], OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, ['array_primitive'|OS1], LVs, NewInstrHandle).
	
local_instr(iinc,state([EE|EEs],CT),state([NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    jpl_call(InstrHandle,getInstruction,[],Instr),
    jpl_call(Instr,getIncrement,[],Increment),
    jpl_call(Instr,getIndex,[],Index),
    get_assoc(Index,LVs,Value),
    put_assoc(Index,LVs,(Value+Increment),NewLVs),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS, NewLVs, NewInstrHandle).
	
put_instr(putstatic, state([EE|EEs],CT), state([NewEE|EEs],NewCT), _Safe) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [O1|OS1] ; (OS = [], OS1 = [])),
	jpl_call('mcparser.instr.InstructionInfo', getFieldOpDataLite, [C, M, InstrHandle], FieldOpData),
    (FieldOpData \== @null ->
        (jpl_get(FieldOpData, fieldName, FieldName),
         jpl_get(FieldOpData, className, ClassName),
         jpl_get(FieldOpData, objType, ObjType),
         jpl_call(ObjType,toString,[],ObjTypeString))
        ;
        (FieldName = 'unknown',
         ClassName = 'unknown',
         ObjTypeString = 'unknown')),

    format('In putstatic, O1 = ~w~n', [O1]),
    format('In putstatic, FieldName = ~w and O1 (Operand Expression) = ~w~n', [FieldName, O1]),

    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle).
	
default_instr(pop, state([EE|EEs],CT), state( [NewEE|EEs],CT)) :-
	EE = env(C, M, OS, LVs, InstrHandle),
    (OS = [_O1|OS1] ; (OS = [] ; OS1 = [])),
    jpl_call(InstrHandle,getNext,[],NewInstrHandle),
	NewEE = env(C, M, OS1, LVs, NewInstrHandle).
	
return_instr(areturn, state([CalleeEE,CallerEE|EEs],CT), state( [NewCallerEE|EEs],CT)) :-
	CalleeEE = env(_C, M, CalleeOS, LVs, _InstrHandle),
    (CalleeOS = [RetVar|_] ; CalleeOS = []),
    % ToString operations need to generate a mapping so we know what object
    % was used to generate the resulting string
    % (Currently we just want the same old variable)
    ((jpl_call(M,getName,[],'toString')) ->
        get_assoc(0,LVs,ObjectVar),
        RetVar = ObjectVar
        ;
        true),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
	NewCallerEE = env(OldC, OldM, [RetVar|OldOS], OldLVs, OldInstrHandle).

return_instr(ireturn, state([CalleeEE,CallerEE|EEs],CT), state( [NewCallerEE|EEs],CT)) :-
	CalleeEE = env(_C, _M, CalleeOS, _LVs, _InstrHandle),
    (CalleeOS = [RetVar|_] ; CalleeOS = []),
	CallerEE = env(OldC, OldM, OldOS, OldLVs, OldInstrHandle),
	NewCallerEE = env(OldC, OldM, [RetVar|OldOS], OldLVs, OldInstrHandle).
