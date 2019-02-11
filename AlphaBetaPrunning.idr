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
     -- MkGrid : Vect 9 (Int, Position) -> Grid
     MkGrid : List (Int, Position) -> Grid
     
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
EmptyGrid = MkGrid [(1,E),(2,E),(3,E),
                    (4,E),(5,E),(6,E),
                    (7,E),(8,E),(9,E)]

nextPlayer : Player -> Player
nextPlayer Cross = Zero 
nextPlayer Zero = Cross
------------------------------------

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
                      
 
-- makeTriples : Vect 9 (Int, Position) -> List (List (Int, Position))
makeTriples : List (Int, Position) -> List (List (Int, Position))
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

checkGrid : Grid -> Maybe Finished
checkGrid (MkGrid xs) = checkTriple $ makeTriples xs

------------------ Minimax below
-- computer plays for zeroes, human (crosses) go first
data Tree = T Grid (List Tree)
data EstimatedTree = ET (Int, Grid) (List EstimatedTree)

partial
Show Tree where
  show (T x xs) = "Node: " ++ show x ++ "/n" ++ "--------" ++ "/n" ++ 
                  (concat $ map show xs) ++ "/n"
 
-- 
convPlayer : Player -> Position
convPlayer Cross = X
convPlayer Zero = O

insertPos : (init_list : List (Int, Position)) -> (Int, Position) -> Player -> List (Int, Position)
insertPos ((a,b) :: xs) (c,d) plr = case a == c of True => (a,(convPlayer plr)) :: xs
                                                   False => (a,b) :: insertPos xs (c,d) plr
insertPos [] _ _ = []                                                   

fillIfEmpty : Player -> (xs : List (Int, Position)) -> (Int, Position) -> List (Int, Position)
fillIfEmpty plr xs (a,b) = case b of E => insertPos xs (a,b) plr
                                     _ => []

delEmptyList : List (List (Int, Position)) -> List (List (Int, Position))
delEmptyList [] = []
delEmptyList (x :: xs) = case length x of Z => delEmptyList xs
                                          _ => x :: (delEmptyList xs)

-- In each inner list 9 elements!
addPlrFreePos : (xs : List (Int, Position)) -> Player -> List (List (Int, Position))
addPlrFreePos xs plr = delEmptyList $ nub $ map (fillIfEmpty plr xs) xs

turnToGrid : List (Int, Position) -> Grid
turnToGrid xs = MkGrid xs

partial
mkTree : Player -> Grid -> Tree 
mkTree player gr@(MkGrid xs) 
 = T gr (map (mkTree (nextPlayer player)) $ map turnToGrid $ addPlrFreePos xs player)

-- bypass tree function 

getMax : (l : List EstimatedTree) -> (acc : Int) -> Int
getMax [] acc = acc
getMax ((ET (a, b) ys) :: xs) acc = case acc >= a of True => getMax xs acc
                                                     False => getMax xs a

getMin : (l : List EstimatedTree) -> (acc : Int) -> Int
getMin [] acc = acc
getMin ((ET (a, b) ys) :: xs) acc = case acc >= a of True => getMin xs a 
                                                     False => getMin xs acc
--data Tree = T Grid (List Tree)
--data EstimatedTree = ET (Int, Grid) (List EstimatedTree)

partial
minimax : Player -> Tree -> EstimatedTree
minimax plr (T grid []) = case checkGrid grid of Just CrLost => ET (100, grid) []
                                                 Just CrWon => ET (-100, grid) []
                                                 Just Dr => ET (0, grid) []
                                                 Nothing => ET (0, grid) [] 
                                             
minimax plr (T grid xs) = let lst = map (minimax (nextPlayer plr)) xs in
                                        case plr of Cross => ET ((getMin lst 0), grid) lst
                                                    Zero => ET ((getMax lst 0), grid) lst 

----------------- Minimax abowe

-- do we already have winning state? Three in a row
data MoveRes = Draw | Won | Cont

data GameState : Type where
     NotRunning : GameState
     Running : (free_pos : Nat) -> (player : Player) -> GameState



-- all possible operations we can run that affect GameState: 
data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
     
     NewGame : Grid -> GameCmd () NotRunning (const (Running 9 Cross))
     CrossesWon : GameCmd () (Running free_pos Cross) (const NotRunning)
     CrossesLost : GameCmd () (Running free_pos Zero) (const NotRunning)
     DrawGame : GameCmd () (Running 0 pl) (const NotRunning)
    
     Move : (move : Int) -> GameCmd MoveRes  
                                (Running free_pos pl)
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
     ReadMove : GameCmd Int (Running (S free_pos) pl) (const (Running free_pos pl))
     EmergencyExit : GameCmd () st (const NotRunning)
     
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
                                                                        EmergencyExit
                                                                        Exit

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
                  (pl : Player) -> (estTree : EstimatedTree) -> Game (Running frp pl)

Show (Game g) where
  show GameStart = "Starting Game"
  show (CrossW grid) = "Zeroes won! \n" ++ show grid
  show (CrossL grid) = "Crosses won! \n" ++ show grid 
  show (JustDraw grid) = "It's a draw! \n" ++ show grid
  show (InProgress grid frps pl esTr) = show pl ++ ", please move \n" ++ "free pos-s: \n" ++ 
                                        show frps ++ "\n" ++ show grid
  
data Fuel = Dry | More (Lazy Fuel) 

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
     OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn
     OutOfFuel : GameResult ty outstate_fn

ok : (res : ty) -> Game (outstate_fn res) -> IO (GameResult ty outstate_fn)
ok res st = pure (OK res st)

---------- for GameCmd Move below --------------------------------------

addMove : Grid -> Int -> Player -> Grid
addMove (MkGrid xs) move pl = MkGrid (map (recordMove move pl) xs) where
                                recordMove : Int -> Player -> (Int, Position) -> (Int, Position)
                                recordMove m p (a,b) = if m /= a then (a,b) 
                                                       else case p of Cross => (a, X)
                                                                      Zero => (a, O)
isValidMove : (str : String) -> Bool
isValidMove str = if (all isDigit (unpack str)) then True else False

removeElem : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later} = y :: removeElem value ys

-- data EstimatedTree = ET (Int, Grid) (List EstimatedTree)
Eq Grid where
  (==) (MkGrid xs1) (MkGrid xs2) = xs1 == xs2

-- gets max-estimated grid from the given list, just one, just upper layer.
getMaxGrid : Grid -> (lst : List EstimatedTree) -> Grid
getMaxGrid gr [] = gr
getMaxGrid gr ((ET (estInt, curGrid) listEstIntsGrids) :: []) = curGrid
getMaxGrid gr ((ET (estInt1, gr1) curGridsForGr1) :: ((ET (estInt2, gr2) curGridsForGr2) :: uppLayerOfGrids)) 
= if estInt1 >= estInt2 
     then getMaxGrid gr1 uppLayerOfGrids
     else getMaxGrid gr2 uppLayerOfGrids

-- gives move, which is the difference between initial and selected grid
compareGrds : (initialGrid : Grid) -> (selectedGrid : Grid) -> Maybe Int
compareGrds (MkGrid xs) (MkGrid ys) = compareLists xs ys where
  commpareLists : List (Int, Position) -> List (Int, Position) -> Maybe Int
  compareLists [] [] = Nothing
  compareLists [] (x :: xs) = Nothing
  compareLists (x :: xs) [] = Nothing
  compareLists ((a, b) :: xs) ((c, d) :: ys)
    = if a == c then case b == d of True => compareLists xs ys
                                    False => Just a
                else Nothing

mutual
  makeMoveHelp : Grid -> List EstimatedTree -> (Maybe Int)
  makeMoveHelp grid [] = Nothing
  makeMoveHelp grid ((ET x ys) :: xs) = ?ss_1


  makeMove : Grid -> EstimatedTree -> Maybe Int
  makeMove grid (ET (estInt, curGrid) listETs) 
    = if grid == curGrid 
      then (compareGrds grid (getMaxGrid grid listETs))
      else makeMoveHelp grid listETs
                                                                                 

---------- for GameCmd Move abowe --------------------------------------
partial
runCmd : Fuel -> Game instate -> GameCmd ty instate outstate_fn -> IO (GameResult ty outstate_fn)
runCmd fuel state (NewGame x) = ok () (InProgress x [1,2,3,4,5,6,7,8,9] _ (minimax Cross (mkTree Cross x))) 
runCmd fuel (InProgress grid frps Cross et) CrossesWon = ok () (CrossW grid)
runCmd fuel (InProgress grid frps Zero et) CrossesLost = ok () (CrossL grid)
runCmd fuel (InProgress grid [] pl et) DrawGame = ok () (JustDraw grid)
runCmd fuel st@(InProgress grid frps pl et) (Move move) 
  = do let newGrid = addMove grid move pl
       case checkGrid newGrid of Just CrLost => ok Won (InProgress newGrid frps (nextPlayer pl) et)
                                 Just CrWon =>  ok Won (InProgress newGrid frps (nextPlayer pl) et)
                                 Just Dr => ok Draw (InProgress newGrid frps (nextPlayer pl) et)
                                 Nothing => ok Cont (InProgress newGrid frps (nextPlayer pl) et)

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
runCmd (More x) st@(InProgress grid frps pl et) ReadMove 
 = if pl == Zero 
   then do putStr "Computer thinking... \n"
           let (Just move) = makeMove grid et
                           | Nothing => do putStrLn "Computer is not able to find solution."
                                           runCmd x st ReadMove
           case isElem move frps of
                Yes prf => ok move (InProgress grid (removeElem move frps) pl et)
                No contra =>  do putStrLn "Position already taken \n"
                                 runCmd x st ReadMove
   else do putStr "Move: "
           inpStr <- getLine
           case isValidMove inpStr of
                  True => case isElem (cast inpStr) frps of 
                               Yes prf => ok (cast inpStr) (InProgress grid (removeElem (cast inpStr) frps) pl et)
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

