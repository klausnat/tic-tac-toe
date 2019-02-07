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

-- do we already have winning state? Three in a row
data MoveRes = Draw | Won | Cont

data GameState : Type where
     NotRunning : GameState
     Running : (free_pos : Nat) -> (player : Player) -> GameState

nextPlayer : Player -> Player
nextPlayer Cross = Zero 
nextPlayer Zero = Cross

-- all possible operations we can run that affect GameState: 
data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
     
     NewGame : Grid -> GameCmd () NotRunning (const (Running 9 Cross))
     CrossesWon : GameCmd () (Running free_pos Cross) (const NotRunning)
     CrossesLost : GameCmd () (Running free_pos Zero) (const NotRunning)
     DrawGame : GameCmd () (Running 0 pl) (const NotRunning)
    
     Move : (move : Int) -> GameCmd MoveRes  
                                (Running (S free_pos) pl)
                                (\res => case res of Draw => (Running free_pos (nextPlayer pl))
                                                     Won => (Running free_pos (nextPlayer pl))
                                                     Cont => (Running free_pos (nextPlayer pl))
                                )
     Pure : (res : ty) -> GameCmd ty (st_fn res) (st_fn)
     (>>=) : GameCmd a st1 st2_fn ->
             ((res : a) -> GameCmd b (st2_fn res) st3_fn) ->
             (GameCmd b st1 st3_fn)
     ShowState : GameCmd () st (const st )
     Message : String -> GameCmd () st (const st)
     ReadMove : GameCmd Int st (const st)

namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
       (>>=) : GameCmd a st1 st2_fn -> 
               ((res : a) -> Inf (GameLoop b (st2_fn res) st3_fn)) ->
               GameLoop b st1 st3_fn
       Exit : GameLoop () NotRunning (const NotRunning)

-- crosses go first   
partial
gameLoop : GameLoop () (Running (S free_pos) player) (const NotRunning)
gameLoop {free_pos} {player} = do ShowState 
                                  g <- ReadMove
                                  res <- Move g
                                  case res of
                                       Draw => case free_pos of Z => do DrawGame
                                                                        ShowState
                                                                        Exit
                                       Won => case player of Cross => case free_pos of (S k) => do CrossesLost 
                                                                                                   ShowState
                                                                                                   Exit
                                                                                       Z => do CrossesLost
                                                                                               ShowState
                                                                                               Exit
                                                             Zero => case free_pos of (S k) => do CrossesWon
                                                                                                  ShowState
                                                                                                  Exit
                                                                                      Z => do CrossesWon
                                                                                              ShowState
                                                                                              Exit
                                       Cont => case free_pos of (S k) => do Message "next"
                                                                            gameLoop
                                                                _ => do Message "Smth is wrong! Game Over"
                                                                        ?ssh

partial                                                                                                
tictactoe : GameLoop () NotRunning (const NotRunning)
tictactoe = do NewGame EmptyGrid
               gameLoop

data Game : GameState -> Type where
     GameStart : Game NotRunning
     CrossW : Grid -> Game NotRunning
     CrossL : Grid -> Game NotRunning
     JustDraw : Grid -> Game NotRunning
     InProgress : Grid -> (frps : Vect frp Int) -> 
                  (pl : Player) -> Game (Running frp pl)

Show (Game g) where
  show GameStart = "Starting Game"
  show (CrossW grid) = "Zeroes won! \n" ++ show grid
  show (CrossL grid) = "Crosses won! \n" ++ show grid 
  show (JustDraw grid) = "It's a draw! \n" ++ show grid
  show (InProgress grid frps pl) = show pl ++ ", please move \n" ++ "free pos-s: \n" ++ 
                                   show frps ++ "\n" ++ show grid
  
data Fuel = Dry | More (Lazy Fuel) 

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
     OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn
     OutOfFuel : GameResult ty outstate_fn

ok : (res : ty) -> Game (outstate_fn res) -> IO (GameResult ty outstate_fn)
ok res st = pure (OK res st)

---------- for GameCmd Move below --------------------------------------

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

data Finished = CrLost | CrWon | Dr

checkTriple : List (List (Int, Position)) -> Maybe Finished
checkTriple xs = if (any chkCross xs) then Just CrWon
                 else if (any chkZero xs) then Just CrLost
                 else if all chkFreePos xs then Just Dr
                 else Nothing where
                              chkCross : List (Int, Position) -> Bool
                              chkCross xs = all (\(int,p) => if p == X then True else False) xs
                              chkZero : List (Int, Position) -> Bool
                              chkZero xs = all (\(int,p) => if p == O then True else False) xs
                              chkFreePos : List (Int, Position) -> Bool
                              chkFreePos xs = all (\(int,p) => if p /= E then True else False) xs

addMove : Grid -> Int -> Player -> Grid
addMove (MkGrid xs) move pl = MkGrid (map (recordMove move pl) xs) where
                                recordMove : Int -> Player -> (Int, Position) -> (Int, Position)
                                recordMove m p (a,b) = if m /= a then (a,b) 
                                                       else case p of Cross => (a, X)
                                                                      Zero => (a, O)

checkGrid : Grid -> Maybe Finished
checkGrid (MkGrid xs) = checkTriple $ makeTriples xs

isValidMove : (str : String) -> Bool
isValidMove str = if (all isDigit (unpack str)) then True else False

removeElem : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later} = y :: removeElem value ys

---------- for GameCmd Move abowe --------------------------------------
partial
runCmd : Fuel -> Game instate -> GameCmd ty instate outstate_fn -> IO (GameResult ty outstate_fn)
runCmd fuel state (NewGame x) = ok () (InProgress x [1,2,3,4,5,6,7,8,9] _) 
runCmd fuel (InProgress grid frps Cross) CrossesWon = ok () (CrossW grid)
runCmd fuel (InProgress grid frps Zero) CrossesLost = ok () (CrossL grid)
runCmd fuel (InProgress grid [] pl) DrawGame = ok () (JustDraw grid)
runCmd fuel st@(InProgress grid frps pl) (Move move) 
  = do let newGrid = addMove grid move pl
       case isElem move frps of
                   Yes prf => case checkGrid newGrid of
                                   Just CrLost => ok Won (InProgress newGrid (removeElem move frps) (nextPlayer pl))
                                   Just CrWon =>  ok Won (InProgress newGrid (removeElem move frps) (nextPlayer pl))
                                   Just Dr => ok Draw (InProgress newGrid (removeElem move frps) (nextPlayer pl))
                                   Nothing => ok Cont (InProgress newGrid (removeElem move frps) (nextPlayer pl))
                   No contra => do putStr "Position already taken \n"
                                   ?ss
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) = do OK cmdRes newSt <- runCmd fuel state cmd
                                          | OutOfFuel => pure OutOfFuel
                                      runCmd fuel newSt (next cmdRes)    
runCmd fuel state ShowState = do printLn state
                                 ok () state
runCmd fuel state (Message str) = do putStrLn str
                                     ok () state
runCmd Dry _ _ = pure OutOfFuel

-- RedMove should check everything, including (isElem inp frps)
runCmd (More x) st@(InProgress grid frps pl) ReadMove 
       = do putStr "Move: "
            inpStr <- getLine
            case isValidMove inpStr of
                 True => case isElem (cast inpStr) frps of 
                              Yes prf => ok (cast inpStr) st
                              No contra =>  do putStrLn "Position already taken \n"
                                               runCmd x st ReadMove
                 False => do putStrLn "Invalid input"
                             runCmd x st ReadMove

partial
run : Fuel -> Game instate -> GameLoop ty instate outstate_fn -> IO (GameResult ty outstate_fn)
run Dry _ _ = pure OutOfFuel
run (More fuel) st (cmd >>= next) = do OK cmdRes newSt <- runCmd fuel st cmd
                                              | OutOfFuel => pure OutOfFuel
                                       run fuel newSt (next cmdRes)
run (More fuel) st Exit = pure (OK () st)


%default partial
forever : Fuel 
forever = More forever

main : IO ()
main = do run forever GameStart tictactoe
          pure ()

