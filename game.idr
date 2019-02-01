import Data.Vect

%default total

data Position = X | O | E

Eq Position where
   (==) X X = True
   (==) O O = True
   (==) E E = True
   (==) _ _ = False
      
data Player = Cross | Zero
Show Player where
  show Cross = "crosses"
  show Zero = "zeroes" 

Eq Player where
   (==) Cross Cross = True
   (==) Zero Zero = True
   (==) _ _ = False 

Show Position where
  show X = "X"
  show O = "O"
  show E = " "

data Grid : Type where 
     MkGrid : Vect 9 (Int, Position) -> Grid

sp : String
sp = " "

vt : String
vt = " | "

showSquare : (Int, Position) -> String
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

-- Vect empty_squares_remaining Int - List of numbers of Empty Squares
data GameState : Type where
     MkGameState : Grid -> List Int -> Player -> GameState

data Finished = CrossesLost | CrossesWon | Draw

isValidMove : (str : String) -> (st : List Int) -> Bool
isValidMove str st = case unpack str of [c] => elem (cast c) st 
                                        _ => False

partial
readMove : GameState -> IO (Int)
readMove st@(MkGameState grid xs pl) = do putStr (show pl ++ ", your move: ")
                                          inpStr <- getLine
                                          case isValidMove inpStr xs of
                                               True => pure (cast inpStr)
                                               False => do putStrLn "Invalid input"
                                                           readMove st
addMove : Grid -> Int -> Player -> Grid
addMove (MkGrid xs) move pl = MkGrid (map (recordMove move pl) xs) where
                                recordMove : Int -> Player -> (Int, Position) -> (Int, Position)
                                recordMove m p (a,b) = if m /= a then (a,b) 
                                                       else case p of Cross => (a, X)
                                                                      Zero => (a, O)
                                
processMove : (move : Int) -> GameState -> GameState
processMove move (MkGameState grid xs pl) = let newGrid = addMove grid move pl
                                                newXs = delete move xs
                                                newPl = if pl == Cross then Zero
                                                                       else  Cross in
                                                MkGameState newGrid newXs newPl

checkFinish : GameState -> Maybe Finished
checkFinish st = ?dd

partial
game : GameState -> IO Finished
game st@(MkGameState gr xs pl) = do mv <- readMove st
                                    let newSt = processMove mv st
                                    case checkFinish newSt of Just a => pure a
                                                              Nothing => game newSt

partial
main : IO ()

{-
main = do result <- game (MkGameState EmptyGrid [1,2,3,4,5,6,7,8,9] Cross)
          case result of CrossesLost => putStrLn "Crosses Lost, Zeroes Win!"
                         CrossesWon => putStrLn "Crosses Win, Zeroes Lost!"
                         Draw => putStrLn "It's a draw!"

-}


