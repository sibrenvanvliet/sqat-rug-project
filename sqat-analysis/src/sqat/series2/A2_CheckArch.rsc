module sqat::series2::A2_CheckArch

import sqat::series2::Dicto;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import Message;
import ParseTree;
import IO;
import List;
import ToString;
import String;
import Set;

/*

This assignment has two parts:
- write a dicto file (see example.dicto for an example)
  containing 3 or more architectural rules for Pacman
  
- write an evaluator for the Dicto language that checks for
  violations of these rules. 

Part 1  

An example is: ensure that the game logic component does not 
depend on the GUI subsystem. Another example could relate to
the proper use of factories.
	The first example is not (easily) possible because we cannot
	check a rule like "jpacman.game cannot depend jpacman.ui" because
	the M3 tree works on class and method levels, we have not been able
	to find the package level.
	The second example is not possible because constraints like
	"only GameFactory can instantiate Game" do not exist in the provided
	language. Furthermore, we would have to write a rule checking this
	for each factory individually, because the provided language does
	not offer regular expressions, so that we could add a rule like
	"only XFactory can instantiate X".

Make sure that at least one of them is violated (perhaps by
first introducing the violation).

Explain why your rule encodes "good" design.
  
Part 2:  
 
Complete the body of this function to check a Dicto rule
against the information on the M3 model (which will come
from the pacman project). 

A simple way to get started is to pattern match on variants
of the rules, like so:

switch (rule) {
  case (Rule)`<Entity e1> cannot depend <Entity e2>`: ...
  case (Rule)`<Entity e1> must invoke <Entity e2>`: ...
  ....
}

Implement each specific check for each case in a separate function.
If there's a violation, produce an error in the `msgs` set.  
Later on you can factor out commonality between rules if needed.

The messages you produce will be automatically marked in the Java
file editors of Eclipse (see Plugin.rsc for how it works).

Tip:
- for info on M3 see series2/A1a_StatCov.rsc.

Questions
- how would you test your evaluator of Dicto rules? (sketch a design)
	A way is to build a very small Java application which encompasses all kinds
	of rules you would like to enforce. Then you generate its M3 tree and look
	manually whether the system complies to your constraints in mind. Then you
	use Dicto with said constraints to see whether its result matches with your
	manually found result.
- come up with 3 rule types that are not currently supported by this version
  of Dicto (and explain why you'd need them).
  	"only ... can ..."
  		See the explanation on game logic-GUI interaction why this would be useful.
  	regular expression rules
  		See the explanation on factories why this would be useful.
  	explicit mention of method calls
  		The provided Dicto language does not accept the use of parantheses.
  		Because M3 does use parentheses to denote the invocations of specific methods
  		(unmissable in cases of polymorphism, where the specific types of arguments
  		decides which method is called) this makes this version of Dicto incapable
  		of putting constraints on method calls.
  	implementing interfaces
  		The provided Dicto language does not have a keyword for creating a constraint
  		that checks whether or not a class implements a certain interface.
*/

set[Declaration] jpacmanASTs() = createAstsFromEclipseProject(|project://jpacman-framework/src|, true);
M3 m3 = createM3FromEclipseProject(|project://jpacman-framework|);

Rule ruleg;
set[Message] msgs = {};
rel[str from, str to, loc src] constructorCalls = {};
rel[str from, str to, loc src] methodCalls = {};

/* Given the string of a location, this function cuts it off at the method level
 * If there is no method in the string, only cut off the closing pipe. */
str truncateToMethod(str s) {
	if (findFirst(s, "(") != -1) {
		return substring(s, 0, findFirst(s, "("));
	} else {
		return substring(s, 0, findLast(s, "|"));
	}
}

/* Given the string of a location, this function cuts it off at the class level */
str truncateToClass(str s) {
	str s2 = truncateToMethod(s);
	return substring(s2, 0, findLast(s2, "/"));
}

/* Given the string of a location, this function cuts off the start, replaces slashes by dots, and removes pipes */
str prettifyLocationString(str s) {
	return replaceAll(replaceAll(substring(s, findFirst(s, ":///")+4), "/", "."), "|", "");
}

/* Same as above, but when given a loc */
str loc2str(loc l) {
	return prettifyLocationString(toString(l));
}

/* Same as above, but when given a loc from an AST instead of an M3 */
str astSrc2str(loc l) {
	str s = toString(l);
	return replaceAll(substring(s, findFirst(s, "/src/main/java/")+15, findFirst(s, ".java")), "/", ".");
}

/* Given an Entity, turn it into a loc by adding a front and changing dots to slashes */
loc entity2loc(Entity e) {
	return |java+class:///| + replaceAll(toString(e), ".", "/");
}

void findConstructorCalls() {
	for (tuple[loc from, loc to] t <- m3@methodInvocation) {
		str from = toString(t.from);
		str to = toString(t.to);
		if (findFirst(to, "java+constructor") != -1) {
			constructorCalls += <prettifyLocationString(truncateToClass(from)), prettifyLocationString(truncateToClass(to)), t.from>;
		}
	}
}

void findMethodCalls() {
	for (tuple[loc from, loc to] t <- m3@methodInvocation) {
		str from = toString(t.from);
		str to = toString(t.to);
		if (findFirst(to, "java+method") != -1) {
			methodCalls += <prettifyLocationString(truncateToClass(from)), prettifyLocationString(truncateToMethod(to)), t.from>;
		}
	}
}

/* The 'Must<Action>' functions add a warning message if
 * e1 does not <Action> e2
 */
void checkMustImport(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	loc l2 = entity2loc(e2);
	bool wasImported = false;
	for (Declaration d <- jpacmanASTs()) {
		visit(d){
			case \import(str name) : {
				if (astSrc2str(d@src) == loc2str(l1) && loc2str(l2) == name) {
					wasImported = true;
					return;
				}
			}
		}
	}
	if (!wasImported) {
		msgs += warning(toString(e1)+" does not import "+toString(e2)+" which violates rule "+toString(ruleg), l1);
	}
}

void checkMustDepend(Entity e1, Entity e2) {
	
}

void checkMustInvoke(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	if (isEmpty(methodCalls[toString(e1)][toString(e2)])) {
		msgs += warning(toString(e1)+" does not invoke "+toString(e2)+" which violates rule "+toString(ruleg), l1);
	}
}

void checkMustInstantiate(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	if (isEmpty(constructorCalls[toString(e1)][toString(e2)])) {
		msgs += warning(toString(e1)+" does not instantiate "+toString(e2)+" which violates rule "+toString(ruleg), l1);
	}
}

void checkMustInherit(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	loc l2 = entity2loc(e2);
	if (m3@extends[l1] != {l2}) {
		msgs += warning(toString(e1)+" does not inherit "+toString(e2)+" which violates rule "+toString(ruleg), l1);
	}
}

/* The 'May' functions are empty because these rules cannot be violated,
 * therefore there are no warning messages to be added.
 */
void checkMayImport(Entity e1, Entity e2) {
}

void checkMayDepend(Entity e1, Entity e2) {
}

void checkMayInvoke(Entity e1, Entity e2) {
}

void checkMayInstantiate(Entity e1, Entity e2) {
}

void checkMayInherit(Entity e1, Entity e2) {
}

/* The 'Cannot<Action>' functions add a warning message if
 * e1 <Action>s e2
 */
void checkCannotImport(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	loc l2 = entity2loc(e2);
	for (Declaration d <- jpacmanASTs()) {
		visit(d){
			case \import(str name) : {
				if (astSrc2str(d@src) == loc2str(l1) && loc2str(l2) == name) {
					msgs += warning(toString(e1)+" imports "+toString(e2)+" which violates rule "+toString(ruleg), l1);
				}
			}
		}
	}
}

void checkCannotDepend(Entity e1, Entity e2) {
}

void checkCannotInvoke(Entity e1, Entity e2) {
	set[loc] invocation = methodCalls[toString(e1)][toString(e2)];
	if (!isEmpty(invocation)) {
		msgs += warning(toString(e1)+" invokes "+toString(e2)+" which violates rule "+toString(ruleg), getOneFrom(invocation));
	}
}

void checkCannotInstantiate(Entity e1, Entity e2) {
	set[loc] instantiation = constructorCalls[toString(e1)][toString(e2)];
	if (!isEmpty(instantiation)) {
		msgs += warning(toString(e1)+" instantiates "+toString(e2)+" which violates rule "+toString(ruleg), getOneFrom(instantiation));
	}
}

void checkCannotInherit(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	loc l2 = entity2loc(e2);
	if (m3@extends[l1] == {l2}) {
		msgs += warning(toString(e1)+" inherits "+toString(e2)+" which violates rule "+toString(ruleg), l1);
	}
}

/* The 'CanOnly<Action>' functions add a warning message if
 * e1 <Action>s eX where eX != e2
 */
void checkCanOnlyImport(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	loc l2 = entity2loc(e2);
	for (Declaration d <- jpacmanASTs()) {
		visit(d){
			case \import(str name) : {
				if (astSrc2str(d@src) == loc2str(l1)) {
					if (loc2str(l2) != name) {
						msgs += warning(toString(e1)+" imports "+name+" which violates rule "+toString(ruleg), l1);
						return;
					}
				}
			}
		}
	}
}

void checkCanOnlyDepend(Entity e1, Entity e2) {
}

void checkCanOnlyInvoke(Entity e1, Entity e2) {
	list[tuple[str to, loc src]] illegalInvocations = [<x,y> | <x,y> <- methodCalls[toString(e1)], x != toString(e2)];
	if (!isEmpty(illegalInvocations)) {
		tuple[str to, loc src] violator = getOneFrom(illegalInvocations);
		msgs += warning(toString(e1)+" invokes "+violator.to+" which violates rule "+toString(ruleg), violator.src);
	}
}

void checkCanOnlyInstantiate(Entity e1, Entity e2) {
	list[tuple[str to, loc src]] illegalInstantiations = [<x,y> | <x,y> <- constructorCalls[toString(e1)], x != toString(e2)];
	if (!isEmpty(illegalInstantiations)) {
		tuple[str to, loc src] violator = getOneFrom(illegalInstantiations);
		msgs += warning(toString(e1)+" instantiates "+violator.to+" which violates rule "+toString(ruleg), violator.src);
	}
}

void checkCanOnlyInherit(Entity e1, Entity e2) {
	loc l1 = entity2loc(e1);
	loc l2 = entity2loc(e2);
	set[loc] superclasses = m3@extends[l1];
	if (superclasses != {} && superclasses != {l2}) {
		msgs += warning(toString(e1)+" inherits "+toString(loc2str(getOneFrom(superclasses)))+" which violates rule "+toString(ruleg), l1);
	}
}

// Call: checkArch();
//set[Message] checkArch() {
void checkArch() {
	msgs = {};
	findConstructorCalls();
	findMethodCalls();
	eval(parse(#start[Dicto], |project://sqat-analysis/src/sqat/series2/constraints.dicto|), m3);
	for (Message m <- msgs) {
		println(m);
		println();
	}
	println(size(msgs));
	//return eval(parse(#start[Dicto], |project://sqat-analysis/src/sqat/series2/constraints.dicto|), m3);
}

set[Message] eval(start[Dicto] dicto, M3 m3) = eval(dicto.top, m3);

set[Message] eval((Dicto)`<Rule* rules>`, M3 m3) 
	= ( {} | it + eval(r, m3) | r <- rules );
  
set[Message] eval(Rule rule, M3 m3) {
	ruleg = rule;
	
	switch (rule) {
		case (Rule)`<Entity e1> must import <Entity e2>`: 			checkMustImport(e1, e2);
		case (Rule)`<Entity e1> must depend <Entity e2>`: 			checkMustDepend(e1, e2);
		case (Rule)`<Entity e1> must invoke <Entity e2>`: 			checkMustInvoke(e1, e2);
		case (Rule)`<Entity e1> must instantiate <Entity e2>`: 		checkMustInstantiate(e1, e2);
		case (Rule)`<Entity e1> must inherit <Entity e2>`: 			checkMustInherit(e1, e2);
		case (Rule)`<Entity e1> may import <Entity e2>`: 			checkMayImport(e1, e2);
		case (Rule)`<Entity e1> may depend <Entity e2>`: 			checkMayDepend(e1, e2);
		case (Rule)`<Entity e1> may invoke <Entity e2>`: 			checkMayInvoke(e1, e2);
		case (Rule)`<Entity e1> may instantiate <Entity e2>`: 		checkMayInstantiate(e1, e2);
		case (Rule)`<Entity e1> may inherit <Entity e2>`: 			checkMayInherit(e1, e2);
		case (Rule)`<Entity e1> cannot import <Entity e2>`: 		checkCannotImport(e1, e2);
		case (Rule)`<Entity e1> cannot depend <Entity e2>`: 		checkCannotDepend(e1, e2);
		case (Rule)`<Entity e1> cannot invoke <Entity e2>`: 		checkCannotInvoke(e1, e2);
		case (Rule)`<Entity e1> cannot instantiate <Entity e2>`: 	checkCannotInstantiate(e1, e2);
		case (Rule)`<Entity e1> cannot inherit <Entity e2>`: 		checkCannotInherit(e1, e2);
		case (Rule)`<Entity e1> can only import <Entity e2>`: 		checkCanOnlyImport(e1, e2);
		case (Rule)`<Entity e1> can only depend <Entity e2>`: 		checkCanOnlyDepend(e1, e2);
		case (Rule)`<Entity e1> can only invoke <Entity e2>`: 		checkCanOnlyInvoke(e1, e2);
		case (Rule)`<Entity e1> can only instantiate <Entity e2>`:	checkCanOnlyInstantiate(e1, e2);
		case (Rule)`<Entity e1> can only inherit <Entity e2>`: 		checkCanOnlyInherit(e1, e2);
	}
	
	return msgs;
}