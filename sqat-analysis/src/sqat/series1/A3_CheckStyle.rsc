module sqat::series1::A3_CheckStyle

import lang::java::\syntax::Java15;
import Message;
import util::FileSystem;
import List;
import IO;
import lang::java::jdt::m3::AST;
import ToString;
import String;

/*

Assignment: detect style violations in Java source code.
Select 3 checks out of this list:  http://checkstyle.sourceforge.net/checks.html
Compute a set[Message] (see module Message) containing 
check-style-warnings + location of  the offending source fragment. 

Plus: invent your own style violation or code smell and write a checker.

Note: since concrete matching in Rascal is "modulo Layout", you cannot
do checks of layout or comments (or, at least, this will be very hard).

JPacman has a list of enabled checks in checkstyle.xml.
If you're checking for those, introduce them first to see your implementation
finds them.

Questions
- for each violation: look at the code and describe what is going on? 
  Is it a "valid" violation, or a false positive?

Tips 

- use the grammar in lang::java::\syntax::Java15 to parse source files
  (using parse(#start[CompilationUnit], aLoc), in ParseTree)
  now you can use concrete syntax matching (as in Series 0)

- alternatively: some checks can be based on the M3 ASTs.

- use the functionality defined in util::ResourceMarkers to decorate Java 
  source editors with line decorations to indicate the smell/style violation
  (e.g., addMessageMarkers(set[Message]))

  
Bonus:
- write simple "refactorings" to fix one or more classes of violations 

*/

/* Checks for methods and constructors which violate the maximum number of parameters (7)
 * See http://checkstyle.sourceforge.net/config_sizes.html#ParameterNumber
 */
set[Message] checkParameterNumber(set[Declaration] decls) {
	set[Message] result = {};
	
	int MAXIMUM_PARAMETER_NUMBER = 7;
	
	for (Declaration d <- decls) {
		visit(d){
			case \method(_,_,parameters,_,_)	: { if (size(parameters) > MAXIMUM_PARAMETER_NUMBER) result += warning("Method number of parameters ("+toString(size(parameters))+") exceeds maximum ("+toString(MAXIMUM_PARAMETER_NUMBER)+")", d@src); }
			case \method(_,_,parameters,_)		: { if (size(parameters) > MAXIMUM_PARAMETER_NUMBER) result += warning("Method number of parameters ("+toString(size(parameters))+") exceeds maximum ("+toString(MAXIMUM_PARAMETER_NUMBER)+")", d@src); }
			case \constructor(_,parameters,_,_)	: { if (size(parameters) > MAXIMUM_PARAMETER_NUMBER) result += warning("Constructor number of parameters ("+toString(size(parameters))+") exceeds maximum ("+toString(MAXIMUM_PARAMETER_NUMBER)+")", d@src); }
		}
	}
	
	return result;
}

/* Checks for source files which violate the maximum number of lines (2000)
 * See http://checkstyle.sourceforge.net/config_sizes.html#FileLength
 * (The site does not specify whether all lines or only SLOC are intended, we are counting all.)
 */
set[Message] checkFileLength(loc project) {
	set[Message] result = {};
	
	int MAXIMUM_FILE_LENGTH = 2000;
	
	set[loc] locs = files(project);
	for (loc l <- locs) {
	  	if (l.extension == "java" && size(readFileLines(l)) > MAXIMUM_FILE_LENGTH) {
	  		result += warning("Length ("+toString(size(readFileLines(l)))+" lines) of file exceeds maximum number of lines ("+toString(MAXIMUM_FILE_LENGTH)+")", l);
	  	}
	}
	
	return result;
}

/* Checks for methods which violate the number of return statements
 * (2 for non-void methods; 1 for void methods)
 * See http://checkstyle.sourceforge.net/config_coding.html#ReturnCount
 */
set[Message] checkReturnCount(set[Declaration] decls) {
	set[Message] result = {};
	
	int MAXIMUM_RETURN_COUNT_NON_VOID = 2;
	int MAXIMUM_RETURN_COUNT_VOID = 1;
	
	for (Declaration d <- decls) {
		visit(d){
			case \method(_,_,_,_,impl) :
			{
				int voidReturnCount = 0;
				int nonVoidReturnCount = 0;
				
				visit(impl) {
					case \return() : voidReturnCount += 1;
					case \return(_) : nonVoidReturnCount += 1;
				}
				
				if (nonVoidReturnCount > MAXIMUM_RETURN_COUNT_NON_VOID) {
					result += warning("Number of return statements ("+toString(nonVoidReturnCount)+") in non-void method exceeds maximum ("+toString(MAXIMUM_RETURN_COUNT_NON_VOID)+")", impl@src);
				} else if (voidReturnCount > MAXIMUM_RETURN_COUNT_VOID) {
					result += warning("Number of return statements ("+toString(voidReturnCount)+") in void method exceeds maximum ("+toString(MAXIMUM_RETURN_COUNT_VOID)+")", impl@src);
				}
			}
		}
	}
	
	return result;
}

/* Checks for lines which exceed the maximum number of characters (80)
 * See http://checkstyle.sourceforge.net/config_sizes.html#LineLength
 * (The site does not specify whether to ignore indentation whitespace or comments; we do not.)
 */
set[Message] checkLineLength(loc project) {
	set[Message] result = {};
	
	int MAXIMUM_LINE_LENGTH = 80;
	
	set[loc] locs = files(project);
	for (loc l <- locs) {
	  	if (l.extension == "java") {
	  		int lineNumber = 0;
	  		for (str line <- readFileLines(l)) {
	  			lineNumber += 1;
	  			int lineLength = size(trim(line));
	  			if (lineLength > MAXIMUM_LINE_LENGTH) {
	  				result += warning("Length ("+toString(lineLength)+") of line "+toString(lineNumber)+" exceeds maximum line length ("+toString(MAXIMUM_LINE_LENGTH)+")", l);
	  			}
	  		}
	  	}
	}
	
	return result;
}

// Use: checkStyle(|project://jpacman-framework/src|);
set[Message] checkStyle(loc project) {
	set[Message] result = {};
	  
	set[Declaration] asts() = createAstsFromEclipseProject(project, true);
	  
	result += checkFileLength(project);
	result += checkLineLength(project);
	result += checkReturnCount(asts());
	result += checkParameterNumber(asts());
	  
	return result;
}
