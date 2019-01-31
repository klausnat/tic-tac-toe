import Data.Vect

%default total

data Position = X | O | E

Show Position where
  show X = "X"
  show O = "O"
  show E = " "

data Grid : Type where 
     MkGrid : Vect 9 (Integer, Position) -> Grid

sp : String
sp = " "

vt : String
vt = " | "

showSquare : (Integer, Position) -> String
showSquare (a,p) = case a of 1 => show p ++ vt
                             2 => show p ++ vt
                             4 => show p ++ vt
                             5 => show p ++ vt
                             7 => show p ++ vt
                             8 => show p ++ vt
                             3 => show p ++ "\n" ++ "----" ++ "----" ++ "-" ++ "\n" 
                             6 => show p ++ "\n" ++ "----" ++ "----" ++ "-" ++ "\n"
                             9 => show p
                             _ => "nothing"
                             
Show Grid where
  show (MkGrid xs) = concat (map showSquare xs)

EmptyGrid : Grid
EmptyGrid = MkGrid [(1,E),(2,E),(3,E),(4,E),(5,E),(6,E),(7,E),(8,E),(9,E)]

data GameState : (empty_squares_remaining : Nat) -> Type where
     MkGameState : Grid -> GameState empty_squares_remaining

data ValidInput : List Char -> Type where
     Move : (c : Char) -> ValidInput [c]

isValidMove : (s : String) -> Dec (ValidInput (unpack s))

isValidInput : (cs : List Char) -> Dec (ValidInput cs)

partial
readMove : IO (x ** ValidInput x)
readMove = do putStr "Move: "
              x <- getLine
              case isValidMove x of
                   Yes prf => pure (_ ** prf)
                   No contra => do putStrLn "Invalid input"
                                   readMove
               

partial
main : IO ()




