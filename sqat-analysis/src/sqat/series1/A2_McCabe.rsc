module sqat::series1::A2_McCabe

import lang::java::jdt::m3::AST;
import IO;
import List;

/*

Construct a distribution of method cylcomatic complexity. 
(that is: a map[int, int] where the key is the McCabe complexity, and the value the frequency it occurs)


Questions:
- which method has the highest complexity (use the @src annotation to get a method's location)
	nextMove() in Inky.java with a CC of 8

- how does pacman fare w.r.t. the SIG maintainability McCabe thresholds?
	All methods are in the 1-10 CC category, labeled 'simple, without much risk'.

- is code size correlated with McCabe in this case (use functions in analysis::statistics::Correlation to find out)? 
  (Background: Davy Landman, Alexander Serebrenik, Eric Bouwers and Jurgen J. Vinju. Empirical analysis 
  of the relationship between CC and SLOC in a large corpus of Java methods 
  and C functions Journal of Software: Evolution and Process. 2016. 
  http://homepages.cwi.nl/~jurgenv/papers/JSEP-2015.pdf)
  
- what if you separate out the test sources?

Tips: 
- the AST data type can be found in module lang::java::m3::AST
- use visit to quickly find methods in Declaration ASTs
- compute McCabe by matching on AST nodes

Sanity checks
- write tests to check your implementation of McCabe

Bonus
- write visualization using vis::Figure and vis::Render to render a histogram.

*/

set[Declaration] jpacmanASTs() = createAstsFromEclipseProject(|project://jpacman-framework/src|, true); 

/* Count branches of method */
int methodComplexity(Statement impl) {
	int branches = 0;
	
	visit(impl) {
		case \assert(_)							: branches += 1;
		case \assert(_,_)						: branches += 1;
		case \do(body,_)						: branches += 1;
		case \foreach(_,_,body)					: branches += 1;
		case \for(_,_,_,body)					: branches += 1;
		case \for(_,_,body)						: branches += 1;
		case \if(_,thenBranch)					: branches += 1;
		case \if(_,thenBranch,elseBranch)		: branches += 1;
		case \case(_)							: branches += 1;
		case \defaultCase()						: branches += 1;
		case \try(body,catchClauses)			: branches += 1;
		case \try(body,catchClauses,\finally)	: branches += 1;
		case \catch(_,body)						: branches += 1;
		case \while(_,body)						: branches += 1;
		case infix(_,"&&",_)					: branches += 1;
		case infix(_,"||",_)					: branches += 1;
	}
	
	return branches + 1;
}

alias CC = rel[loc method, int cc];


// run with: cc(jpacmanASTs())
CC cc(set[Declaration] decls) {
	CC result = {};
	
	/* Compute complexities for all statements in all declarations */
	for (Declaration d <- decls) {
		visit(d){
			case \method(_,_,_,_,impl) : result += {<d@src, methodComplexity(impl)>};
		}
	}
	  
	return result;
}

alias CCDist = map[int cc, int freq];

// run with: ccDist(cc(jpacmanASTs()))
CCDist ccDist(CC cc) {
	CCDist result = ();
	
	list[int] complexities = [x | <_, int x> <- cc];
	
	for (int i <- [1..max(complexities)+1]) {
		result[i] = 0;
	}
	
	for (int complexity <- complexities) {
		result[complexity] += 1;
	}
	
	return result;
}
