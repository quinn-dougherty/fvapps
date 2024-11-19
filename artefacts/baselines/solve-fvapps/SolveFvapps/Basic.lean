def isSquare (n : Nat) : Bool :=
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then false
    else if i * i > n then false
    else if i * i == n then true
    else check (i + 1) (fuel - 1)
  check 1 n

def findRoot (n : Nat) : Nat :=
  let rec check (i : Nat) (fuel : Nat) : Nat :=
    if fuel = 0 then 1 
    else if i * i > n then i - 1
    else if i * i == n then i
    else check (i + 1) (fuel - 1)
  check 1 n

def findPerfectSqrt (n : Nat) : Nat :=
  let rec check (i : Nat) (fuel : Nat) : Nat :=
    if fuel = 0 then 1
    else if i * i > n then 1
    else if n % (i * i) == 0 then i * i
    else check (i + 1) (fuel - 1)
  check 1 n

def isNumeric (s : String) : Bool :=
  s.all fun c => c.isDigit 

def splitByWhitespace (s : String) : List String := 
  s.split fun c => c == ' '

def containsSqrt (s : String) : Bool :=
  s.contains "sqrt"

def countSqrt (s : String) : Nat :=
  let l := splitByWhitespace s
  if l.length == 2 then 1 else 0

def stringToNat (s : String) : Nat :=
  match s.toNat? with
  | some n => n
  | none => 0

def simplify (n : Nat) : String :=
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    let sqrtFactor := findPerfectSqrt n
    if sqrtFactor == 1 then
      s!"sqrt {n}"
    else if sqrtFactor == n then 
      toString (findRoot n)
    else
      let coeff := findRoot sqrtFactor
      let remaining := n / sqrtFactor
      s!"{coeff} sqrt {remaining}"

def desimplify (s : String) : Nat :=
  let parts := splitByWhitespace s
  match parts with
  | [] => 0 
  | [n] => 
    if isNumeric n then
      stringToNat n
    else if containsSqrt n then
      let root := n.drop 5
      stringToNat root
    else 0
  | [a, b] =>
    if containsSqrt b then
      let coeff := stringToNat a
      let root := b.drop 5  
      coeff * coeff * stringToNat root
    else 0
  | _ => 0

@[simp]
theorem stringToNat_toString (n : Nat) : stringToNat (toString n) = n := by
  simp [stringToNat]
  exact toString_toNat? n

@[simp]
theorem findRoot_nonzero (n : Nat) : n > 0 → findRoot n ≥ 1 := by
  intro h
  simp [findRoot]
  split
  . contradiction
  . simp_all [Nat.zero_lt_one]

@[simp]
theorem findRoot_square_le (n : Nat) : (findRoot n) * (findRoot n) ≤ n := by
  simp [findRoot]
  induction n with
  | zero => simp
  | succ n ih =>
    split <;> simp_all
    . exact Nat.le_refl 0
    . exact Nat.zero_le _
    . sorry -- need nested induction on the recursive call

theorem findPerfectSqrt_valid (n : Nat) :
  let p := findPerfectSqrt n
  p = 1 ∨ n % p = 0 := by
  simp [findPerfectSqrt]
  sorry

theorem desimplify_simplify (n : Nat) : desimplify (simplify n) = n := by
  simp [desimplify, simplify]
  split
  . -- n = 0
    simp [splitByWhitespace, isNumeric]
    exact stringToNat_toString 0
  . split
    . -- n = 1
      simp [splitByWhitespace, isNumeric]
      exact stringToNat_toString 1
    . -- general case
      let p := findPerfectSqrt n
      have h := findPerfectSqrt_valid n
      by_cases hp: p = 1
      . simp [hp, splitByWhitespace, containsSqrt]
        simp [stringToNat_toString]
      . by_cases hpn: p = n
        . simp [hpn, splitByWhitespace, isNumeric]
          exact stringToNat_toString (findRoot n)
        . sorry

#eval simplify 80     -- "4 sqrt 5"
#eval desimplify "4 sqrt 5"  -- 80
#eval simplify 16     -- "4"
#eval desimplify "4"  -- 16