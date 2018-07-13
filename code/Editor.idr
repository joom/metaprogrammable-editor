module Editor

import Language.Reflection.Editor

%access public export

data Editor = Emacs | Vim | VSCode | Atom

export
data Edit : Type -> Type where
  Prim__Pure : a -> Edit a
  Prim__Bind : Edit a -> (a -> Edit b) -> Edit b

  Prim__Try : Edit a -> Edit a -> Edit a
  Prim__TryCatch : Edit a -> (Err -> Edit a) -> Edit a
  Prim__Fail : List ErrorReportPart -> Edit a

  Prim__LiftElab : Elab a -> Edit a

  -- Long list of primitives
  Prim__GetCursorPosition : Edit (Nat, Nat)
  Prim__GetEditor : Edit Editor
  Prim__MoveCursorToColumn : Nat -> Edit ()
  Prim__SetMark : Edit ()
  Prim__DeactivateMark : Edit ()
  Prim__GetLineLength : Edit Nat
  Prim__GetSelection : Edit String
  Prim__Insert : String -> Edit ()

  Prim__ForwardChar : Nat -> Edit ()
  Prim__BackwardChar : Nat -> Edit ()
  Prim__PreviousLine : Nat -> Edit ()
  Prim__NextLine : Nat -> Edit ()

implementation Functor Edit where
  map f t = Prim__Bind t (\x => Prim__Pure (f x))

implementation Applicative Edit where
  pure x  = Prim__Pure x
  f <*> x = Prim__Bind f $ \g =>
            Prim__Bind x $ \y =>
            Prim__Pure   $ g y

implementation Monad Edit where
  x >>= f = Prim__Bind x f

implementation Alternative Edit where
  empty   = Prim__Fail [TextPart "empty"]
  x <|> y = Prim__Try x y

export
liftElab : Elab a -> Edit a
liftElab = Prim__LiftElab

export
getCursorPosition : Edit (Nat, Nat)
getCursorPosition = Prim__GetCursorPosition

export
getEditor : Edit Editor
getEditor = Prim__GetEditor

export
moveCursorToColumn : Nat -> Edit ()
moveCursorToColumn = Prim__MoveCursorToColumn

export
setMark : Edit ()
setMark = Prim__SetMark

export
deactivateMark : Edit ()
deactivateMark = Prim__DeactivateMark

export
getLineLength : Edit Nat
getLineLength = Prim__GetLineLength

export
getSelection : Edit String
getSelection = Prim__GetSelection

export
insert : String -> Edit ()
insert = Prim__Insert
