printlist_vertically(List, Name) :-
	open('out.txt',write,Stream),
	write(Stream,'\n\nPrinting List: ~w~n', [Name]),
	help_printlist(List),
	write(Stream,'\n\n'),
	close(Stream).
help_printlist([L1|Ls]) :-
	open('out.txt',write,Stream),
	write(Stream,L1),
	help_printlist(Ls),
	close(Stream).
help_printlist([]).
getConstantPool([]).
getConstantPool(Class,ConstantPool2) :-
	ConstantPool2 = jpl_call('mcparser.instr.InstructionInfo',getConstantPoolFromClass,Class,ConstantPool).



% arraylist_to_list(+ArrayList,-List)
% Transforms a Java ArrayList
% object into a Prolog List. Can also be used for other kinds of
% Java Collections objects, like Sets. (Really, anything with
% an implementation of toArray) A very useful utility predicate.
arraylist_to_list(ArrayList,List) :-
    jpl_call(ArrayList,toArray,[],Array),
    jpl_array_to_list(Array,List).

list_to_indexed_assoc(List,Assoc) :-

	generate_key_value_pairs(0,List,KeyValuePairList),
	list_to_assoc(KeyValuePairList,Assoc),
	format('KeyValuePairList is: ~w~n',KeyValuePairList).



generate_key_value_pairs(_,[],[]).
generate_key_value_pairs(I,[X|Y],[KeyValuePair|KeyValuePairList]) :-
	KeyValuePair = I-X,
	I1 is I + 1,
	generate_key_value_pairs(I1,Y,KeyValuePairList).
