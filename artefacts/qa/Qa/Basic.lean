def getFirstChar (s : String) : Char :=
  s.get 0

def getLastChar (s : String) : Char :=
  s.get (s.length - 1)

def reverseString (s : String) : String :=
  String.mk (s.data.reverse)

structure State where
  zo : Nat := 0
  oz : Nat := 0
  zz : Nat := 0
  oo : Nat := 0
  zos : List Nat := []
  ozs : List Nat := []
  zoss : List String := []
  ozss : List String := []
deriving Repr

def processWord (state : State) (word : String) (i : Nat) : State :=
  if getFirstChar word == '0' && getLastChar word == '1' then
    { state with 
      zo := state.zo + 1,
      zos := state.zos ++ [i + 1],
      zoss := state.zoss ++ [word] }
  else if getFirstChar word == '1' && getLastChar word == '0' then
    { state with
      oz := state.oz + 1,
      ozs := state.ozs ++ [i + 1],
      ozss := state.ozss ++ [word] }
  else if getFirstChar word == '0' && getLastChar word == '0' then
    { state with zz := state.zz + 1 }
  else
    { state with oo := state.oo + 1 }

def solve_word_reversal (n : Nat) (words : List String) : List Nat := 
  let initState : State := { }
  let state := (List.range n).foldl (fun st i => 
    match words.get? i with
    | some word => processWord st word i
    | none => st
  ) initState

  if state.zz > 0 && state.oo > 0 && state.oz == 0 && state.zo == 0 then
    [0]
  else if state.zo > state.oz then
    let need := (state.zo - state.oz) / 2
    let indices := state.zos.take need
    [indices.length] ++ indices
  else
    let need := (state.oz - state.zo) / 2
    let indices := state.ozs.take need
    [indices.length] ++ indices

#eval solve_word_reversal 4 ["0001", "1000", "0011", "0111"]
#eval solve_word_reversal 3 ["010", "101", "0"] 
#eval solve_word_reversal 2 ["00000", "00001"]