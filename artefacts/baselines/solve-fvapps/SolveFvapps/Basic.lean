def listUnion (l1 l2 : List Char) : List Char :=
  l1.foldl (fun acc x => if x ∈ acc then acc else x :: acc) l2

def listIndexOf (l : List Char) (x : Char) : Nat :=
  match l.findIdx? (· == x) with
  | some i => i
  | none => l.length

def insertSorted (l : List Char) (x : Char) (lt : Char → Char → Bool) : List Char :=
  match l with
  | [] => [x]
  | y :: ys => if lt x y then x :: l else y :: insertSorted ys x lt

def insertionSort (l : List Char) (lt : Char → Char → Bool) : List Char :=
  l.foldl (fun acc x => insertSorted acc x lt) []

def recoverSecret (triplets : List (List Char)) : String :=
  let chars := triplets.foldl listUnion []
  let orderedChars := insertionSort chars (fun a b =>
    triplets.any (fun t => listIndexOf t a < listIndexOf t b))
  String.mk orderedChars

def isConsistentWithTriplets (result : String) (triplets : List (List Char)) : Bool :=
  triplets.all fun t => 
    t.length == 3 && 
    result.data.indexOf t[0]! < result.data.indexOf t[1]! && 
    result.data.indexOf t[1]! < result.data.indexOf t[2]!

def containsAllChars (result : String) (triplets : List (List Char)) : Bool :=
  let allChars := triplets.foldl listUnion []
  allChars.all (·∈ result.data)

theorem recoverSecret_produces_string (triplets : List (List Char)) :
  String.length (recoverSecret triplets) > 0 := by
  sorry

theorem recoverSecret_contains_all_chars (triplets : List (List Char)) : 
  containsAllChars (recoverSecret triplets) triplets = true := by
  sorry

theorem recoverSecret_consistent_with_triplets (triplets : List (List Char)) :
  isConsistentWithTriplets (recoverSecret triplets) triplets = true := by
  sorry

theorem recoverSecret_basic_case :
  recoverSecret [['a', 'b', 'c'], ['a', 'c', 'd']] = "abcd" := by
  sorry

theorem recoverSecret_complex_case :
  recoverSecret [
    ['t','u','p'], 
    ['w','h','i'],
    ['t','s','u'],
    ['a','t','s'],
    ['h','a','p'],
    ['t','i','s'],
    ['w','h','s']
  ] = "whatisup" := by
  sorry