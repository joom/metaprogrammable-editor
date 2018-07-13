module Example

import Editor

%access public export

duplicateLine : Edit ()
duplicateLine =
  do moveCursorToColumn 1
     setMark
     lineEnd <- getLineLength
     moveCursorToColumn lineEnd
     line <- getSelection
     deactivateMark
     insert "\n"
     insert line

upperChar : Edit ()
upperChar =
  do setMark
     s <- getSelection
     deactivateMark
     insert s



