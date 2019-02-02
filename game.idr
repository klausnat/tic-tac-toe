import Data.Vect
import Debug.Trace

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
record GameState where
       constructor MkGameState 
       grid : Grid
       player : Player

data Finished = CrossesLost | CrossesWon | Draw

isValidMove : (str : String) -> Bool
isValidMove str = if (all isDigit (unpack str)) then True else False

partial
readMove : GameState -> IO (Int)
readMove st@(MkGameState grid pl) = do putStr (show pl ++ ", your move: ")
                                       inpStr <- getLine
                                       case isValidMove inpStr of
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
processMove move (MkGameState grid pl) = let newGrid = addMove grid move pl
                                             newPl = if pl == Cross then Zero
                                                                    else Cross in
                                             MkGameState newGrid newPl

makeVerTriples : List (Int, Position) ->
                 List (Int, Position) -> 
                 List  (Int, Position) ->
                 List (List (Int, Position))
makeVerTriples [] [] [] = []
makeVerTriples (x :: xs) (y :: ys) (z :: zs) 
  = (x :: y :: z :: Nil) :: ( makeVerTriples xs ys zs)
makeVerTriples _ _ _ = []

makeDiags : List (Int,Position) -> List (List (Int, Position))
makeDiags xs = (filter check1 xs) :: (filter check2 xs) :: Nil where
                      check1 : (Int,Position) -> Bool
                      check1 (num, p) = if (num == 1 || num == 5 || num == 9) then True else False
                      check2 : (Int,Position) -> Bool
                      check2 (num, p) = if (num == 3 || num == 5 || num == 7) then True else False
                      
 
makeTriples : Vect 9 (Int, Position) -> List (List (Int, Position))
makeTriples xs 
  = let (threeVert1, six) = splitAt 3 xs
        (threeVert2, threeVert3) = splitAt 3 six in
        [toList threeVert1, toList threeVert2, toList threeVert3] ++ 
        makeVerTriples (toList threeVert1) (toList threeVert2) (toList threeVert3) ++ 
        makeDiags (toList xs)

checkTriple : List (List (Int, Position)) -> Maybe Finished
checkTriple xs = if (any chkCross xs) then Just CrossesWon
                 else if (any chkZero xs) then Just CrossesLost
                 else if all chkFreePos xs then Just Draw
                 else Nothing where
                              chkCross : List (Int, Position) -> Bool
                              chkCross xs = all (\(int,p) => if p == X then True else False) xs
                              chkZero : List (Int, Position) -> Bool
                              chkZero xs = all (\(int,p) => if p == O then True else False) xs
                              chkFreePos : List (Int, Position) -> Bool
                              chkFreePos xs = all (\(int,p) => if p /= E then True else False) xs

checkGrid : Grid -> Maybe Finished
checkGrid (MkGrid xs) = checkTriple $ makeTriples xs

checkFinish : GameState -> Maybe Finished
checkFinish (MkGameState grid pl) = checkGrid grid 

partial
game : GameState -> IO Finished
game st@(MkGameState gr pl) = do putStrLn (show gr ++ "\n")
                                 mv <- readMove st
                                 let newSt = processMove mv st
                                 case checkFinish newSt of Just a => do putStrLn (show (grid newSt) ++ "\n")
                                                                        pure a
                                                           Nothing => game newSt

partial
main : IO ()

main = do result <- game (MkGameState EmptyGrid Cross)
          case result of CrossesLost => putStrLn "Crosses Lost, Zeroes Win!"
                         CrossesWon => putStrLn "Crosses Win, Zeroes Lost!"
                         Draw => putStrLn "It's a draw!"




