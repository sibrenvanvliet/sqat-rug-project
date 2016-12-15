module sqat::series1::A1_SLOC

import IO;
import List;
import Set;
import util::FileSystem;
import String;

/* 

Count Source Lines of Code (SLOC) per file:
- ignore comments
- ignore empty lines

Tips
- use locations with the project scheme: e.g. |project:///jpacman/...|
- functions to crawl directories can be found in util::FileSystem
- use the functions in IO to read source files

Answer the following questions:
- what is the biggest file in JPacman?
	Level.java at 179 SLOC
- what is the total size of JPacman?
	2458 SLOC
- is JPacman large according to SIG maintainability?
	No, the range 0-66 kSLOC is considered ++ (very small) by SIG
- what is the ratio between actual code and test code size?
	Actual code is 1901 SLOC (77%), test code is 557 SLOC (23%)

Sanity checks:
- write tests to ensure you are correctly skipping multi-line comments
	(like Series 0)
- and to ensure that consecutive newlines are counted as one.
- compare you results to external tools sloc and/or cloc.pl

Bonus:
- write a hierarchical tree map visualization using vis::Figure and 
  vis::Render quickly see where the large files are. 
  (https://en.wikipedia.org/wiki/Treemapping) 

*/

alias SLOC = map[loc file, int sloc];

int nLinesOfCode(str file) {
	/* First, we remove all multiline comments. */
	while (findFirst(file, "/*") != -1) {
		int multilineCommentStart = findFirst(file, "/*");
		int multilineCommentEnd = findFirst(file, "*/") + 2;
		str multilineComment = substring(file, multilineCommentStart, multilineCommentEnd);
		
		/* Construct file without the found multiline comment */
		str fileWithoutComment = substring(file, 0, multilineCommentStart);
		if (contains(multilineComment, "\n")) {
			fileWithoutComment += "\n";
		}
		if (size(file) > multilineCommentEnd) {
			fileWithoutComment += substring(file, multilineCommentEnd + 1);
		}
		
		file = fileWithoutComment;
	}
	
	/* At this stage, multiline comments are removed.
	 * We now remove lines containing only whitespace or single-line comments.
	 */
	list[str] trimmedLines = [trim(x) | x <- split("\n", file)];
	list[str] nonemptyLines = [s | s <- trimmedLines, !isEmpty(s), !startsWith(s, "//")];
	
	return size(nonemptyLines);
}

// Use: sloc(|project://jpacman-framework/src|);
SLOC sloc(loc project) {
  SLOC result = ();
  
  set[loc] locs = files(project);
  
  for (loc l <- locs) {
  	if (l.extension == "java") {
  		result[l] = nLinesOfCode(readFile(l));
  	}
  }
  
  return result;
}

/* Tests */
test bool testSLOC1()
  = nLinesOfCode("code();\n\n\n\n\t\n//comment\n")
  == 1;

test bool testSLOC2()
  = nLinesOfCode("code(); /* start multiline comment\nthis line is completely inside the multiline comment\nend of multiline comment*/ code();\n")
  == 2;

test bool testSLOC3()
  = nLinesOfCode("code(); /* start\ncomment\nend */ code();\n")
  == 2;

test bool testSLOC4()
  = nLinesOfCode("code(); /* start\ncomment\nend */ /* start\nend */ code();")
  == 2;

test bool testSLOC5()
  = nLinesOfCode("code(); /* start\ncomment\nend */ code(); /* start\nend */ code();")
  == 3;

test bool testSLOC6()
  = nLinesOfCode("code(); /* start\ncomment\nend */ /* small comment */ code();\n")
  == 2;