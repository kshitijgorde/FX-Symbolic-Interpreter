:- use_module(library(lists)).
:- use_module(library(charsio)).
:- use_module(library(jpl)).
:- use_module(library(assoc)).

:- ['Difference_interp_LV_OS'].
:- ['utility'].

set_breakpoints :- 
	spy(help_instr).

jar_to_load('c:/Users/kshit/Desktop/SyntheticKeylogger.jar').
fxp(JarProcessor) :-
	%write(X),
	%write("Hello"),
	open('out.txt',write,Stream),
	%write("Hello"),
	jar_to_load(JARFileName),
	nl(Stream),
    format(Stream,'Loading JAR ~w~n',[JARFileName]),
    jpl_new('mcparser.JarProcessor',[JARFileName],JarProcessor),	
    format(Stream,'Finished loading JAR ~w~n',[JARFileName]),
	jpl_call('mcparser.ParserOutput',setOutFile,['c:/Users/kshit/Desktop/ViewerOutput.txt'],_),
	jpl_call('mcparser.ClassCache',getClassList,[],ClassStringArray),
	jpl_array_to_list(ClassStringArray,ClassStringList),
	format('class string array is = ~w~n',[ClassStringList]),
	jpl_get(ClassStringArray,length,NumClasses),
	format(Stream,'~nTotal Classes: ~w~n',[NumClasses]),
	close(Stream),
	%write(ClassStringList),
	process_classes(ClassStringList).

add_jar_to_classpath(Filename) :-
   (getenv('CLASSPATH', Old)-> true; Old = '.'),
   (current_prolog_flag(windows, true)-> Separator = ';'; Separator = ':'),
   concat_atom([Filename, Old], Separator, New),
   setenv('CLASSPATH', New).

test :- 
	%set_breakpoints,
	fxp(JarProcessor).


