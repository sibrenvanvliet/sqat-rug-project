module sqat::series2::A1a_StatCov

import lang::java::jdt::m3::Core;
import IO;
import String;
import Relation;
import Set;

/*

Implement static code coverage metrics by Alves & Visser 
(https://www.sig.eu/en/about-sig/publications/static-estimation-test-coverage)


The relevant base data types provided by M3 can be found here:

- module analysis::m3::Core:

rel[loc name, loc src]        M3@declarations;            // maps declarations to where they are declared. contains any kind of data or type or code declaration (classes, fields, methods, variables, etc. etc.)
rel[loc name, TypeSymbol typ] M3@types;                   // assigns types to declared source code artifacts
rel[loc src, loc name]        M3@uses;                    // maps source locations of usages to the respective declarations
rel[loc from, loc to]         M3@containment;             // what is logically contained in what else (not necessarily physically, but usually also)
list[Message]                 M3@messages;                // error messages and warnings produced while constructing a single m3 model
rel[str simpleName, loc qualifiedName]  M3@names;         // convenience mapping from logical names to end-user readable (GUI) names, and vice versa
rel[loc definition, loc comments]       M3@documentation; // comments and javadoc attached to declared things
rel[loc definition, Modifier modifier] M3@modifiers;      // modifiers associated with declared things

- module  lang::java::m3::Core:

rel[loc from, loc to] M3@extends;            // classes extending classes and interfaces extending interfaces
rel[loc from, loc to] M3@implements;         // classes implementing interfaces
rel[loc from, loc to] M3@methodInvocation;   // methods calling each other (including constructors)
rel[loc from, loc to] M3@fieldAccess;        // code using data (like fields)
rel[loc from, loc to] M3@typeDependency;     // using a type literal in some code (types of variables, annotations)
rel[loc from, loc to] M3@methodOverrides;    // which method override which other methods
rel[loc declaration, loc annotation] M3@annotations;

Tips
- encode (labeled) graphs as ternary relations: rel[Node,Label,Node]
- define a data type for node types and edge types (labels) 
- use the solve statement to implement your own (custom) transitive closure for reachability.

Questions:
- what methods are not covered at all?
	There are 90 uncovered methods. Please run the method 'printUncoveredMethods();'
- how do your results compare to the jpacman results in the paper? Has jpacman improved?
	In the paper, the static coverage was 88.06%, and the Clover coverage was 93.53%.
	With our analysis, the static coverage is 61.70%.
- use a third-party coverage tool (e.g. Clover) to compare your results to (explain differences)
	We installed Clover and played six games of Pacman in order to do everything possible in the game.
	(Winning the game, dying on each different enemy, pausing and resuming the game, closing mid-game, map warping.)
	Clover resulted in a dynamic coverage of 72.81 % (55 classes, 873 / 1199 elements).
	
	We then used Clover to run the jUnit test suite. Note that the results of playing the game
	were combined with the test suite coverage.
	This resulted in a coverage of 75.56 % (55 classes, 906 / 1199 elements).
	
	Finally, we used Clover to determine the jUnit test suite coverage without considering the
	code coverage of manual gameplay.
	This resulted in a coverage of 71.81 % (55 classes, 861 / 1199 elements).
	
	The difference between our static coverage (61.70%) and the Clover coverage (71.81%) can
	be explained as follows: Our approach looks for each method in production code whether
	it is called at all through the test code. Meanwhile, Clover looks at each line of
	production code individually and keeps track of whether that line was visited/executed or not
	during a dynamic run of the test suite. As a result, the Clover coverage will be lower in
	methods that are called but not completely covered on the inside (while our static coverage
	marks any called function as 100%), and the Clover coverage will be higher in visited/executed
	code outside of methods, because we do not check for coverage of such. The fact that the
	Clover coverage is significantly higher than our static coverage, means that there is a lot
	of code outside of methods which Clover tests while we do not.
*/

M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework/src/|);
alias Node = tuple[loc src1, loc src2];
alias Graph = rel[loc from, loc to];

Graph G, Gtc;
set[Node] T = {};
set[loc] MM = {}, M = {};

/*
 * Step 1: extraction.
 * This step extracts from the M3 model:
 * G, a call graph,
 * (and Gtc, the transitive closure of G),
 * MM, a set of main methods, and
 * T, a set of test methods.
 */
void extract() {
	// Create G
	G = jpacmanM3()@methodInvocation;
	Gtc = G+;
	
	// Populate T
	for (Node n <- jpacmanM3()@declarations) {
		if (isMethod(n.src1)) {
			if (contains(n.src2.path, "/test/")) {
				T += n;
			} else {
				MM += n.src1;
			}
		}
	}
}

/*
 * Step 2: slicing.
 * In this step, we construct M, the set of main methods from G covered by tests in T.
 */
void slice() {
	for (loc t <- [x.src1 | x <- T]) {
		M += Gtc[t] & MM;
	}
}

/*
 * Step 3: counting.
 * In this step, we count the number of main methods and the number of covered methods.
 * (We do this only at the project level, not per class.)
 */
void count() {
	print("Number of methods in production code: ");
	println(size(MM));
	print("Number of methods reached by test code: ");
	println(size(M));
}

/*
 * Step 4: estimation.
 * In this step, we conclude how many main methods are not covered by the test code
 * and give an approximate percentage of covered/uncovered code.
 * (We do this only at the project level, not per class.)
 */
void estimate() {
	int rp =  10000 * size(M) / size(MM);
	real reachedPercent = rp / 100.0;
	
	print("Number of uncovered production methods: ");
	println(size(MM - M));
	print("Final estimation: ");
	print(reachedPercent);
	print("% covered / ");
	print(100.0 - reachedPercent);
	println("% uncovered.");
}

void statCov() {
	extract();
	slice();
	count();
	estimate();
}

void printUncoveredMethods() {
	statCov();
	println("\nUncovered methods:");
	for (loc m <- MM-M) {
		println(m);
	}
}