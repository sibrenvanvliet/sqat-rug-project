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
	2457 SLOC
- is JPacman large according to SIG maintainability?
	No, the range 0-66 kSLOC is considered ++ (very small) by SIG
- what is the ratio between actual code and test code size?
	Actual code is 1900 SLOC (77%), test code is 557 SLOC (23%)

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

SLOC sloc(loc project) {
  SLOC result = ();
  
  set[loc] locs = files(project);
  
  // TODO use flags for better parsing
  
  for (loc l <- locs) {
  	if (l.extension == "java") {
  		list[str] trimmedLines = [trim(s) | s <- readFileLines(l)];
  		list[str] sourceLines = [s | s <- trimmedLines, !isEmpty(s), !startsWith(s, "/*"), !startsWith(s, "*"), !startsWith(s, "//")];
  		result[l] = size(sourceLines);
  	}
  }
  
  return result;
}