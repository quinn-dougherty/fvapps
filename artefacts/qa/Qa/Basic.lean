structure WordCounts where
  zo : Nat := 0  -- 0->1
  oz : Nat := 0  -- 1->0
  zz : Nat := 0  -- 0->0
  oo : Nat := 0  -- 1->1
  ozs : List Nat := []  -- indices of 1->0 words
  zos : List Nat := []  -- indices of 0->1 words
  ozss : List String := []  -- list of 1->0 words 
  zoss : List String := []  -- list of 0->1 words

def solve (n : Nat) (words : List String) : List Nat := 
  -- Initialize counters and lists
  let counts := Id.run do
    let mut c : WordCounts := {}
    for i in [0:n] do
      let word := words[i]!
      if word.front == '0' && word.back == '1' then
        c := {c with 
          zo := c.zo + 1,
          zos := c.zos ++ [i + 1],
          zoss := c.zoss ++ [word]
        }
      else if word.front == '1' && word.back == '0' then
        c := {c with 
          oz := c.oz + 1,
          ozs := c.ozs ++ [i + 1],
          ozss := c.ozss ++ [word]
        }
      else if word.front == '0' && word.back == '0' then
        c := {c with zz := c.zz + 1}
      else
        c := {c with oo := c.oo + 1}
    c

  -- Handle special case
  if counts.zz > 0 && counts.oo > 0 && counts.oz == 0 && counts.zo == 0 then
    [-1]
  else if counts.zo > counts.oz then
    Id.run do
      let mut ans := []
      let mut need := (counts.zo - counts.oz) / 2
      let mut i := 0
      while need > 0 do
        let word := words[counts.zos[i]! - 1]!
        let rev := String.mk (word.data.reverse)
        if !counts.ozss.contains rev then
          ans := ans ++ [counts.zos[i]!]
          need := need - 1
        i := i + 1
      [ans.length] ++ ans
  else 
    Id.run do
      let mut ans := []
      let mut need := (counts.oz - counts.zo) / 2
      let mut i := 0
      while need > 0 do
        let word := words[counts.ozs[i]! - 1]!
        let rev := String.mk (word.data.reverse)
        if !counts.zoss.contains rev then
          ans := ans ++ [counts.ozs[i]!]
          need := need - 1
        i := i + 1
      [ans.length] ++ ans

/--
info: [1, 3]
-/
#guard_msgs in
#eval solve 4 ["0001", "1000", "0011", "0111"]

/--
info: [-1]
-/
#guard_msgs in
#eval solve 3 ["010", "101", "0"]

/--
info: [0]
-/
#guard_msgs in
#eval solve 2 ["00000", "00001"]
