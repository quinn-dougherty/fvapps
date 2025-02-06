import Plausible

import Plausible

import Lean

/-- Helper to count occurrences of char in string -/
def countChar (str : String) (c : Char) : Nat :=
  str.toList.filter (· == c) |>.length

/-- Return list of words matching criteria for vowels, consonants and forbidden chars -/
def wanted_words (vowels consonants : Nat) (forbidden : List Char) : Array String := Id.run do
  let WORD_LIST := #["strength", "afterwards", "background", "photograph", "successful", "understand"]
  let vowel_chars := ['a', 'e', 'i', 'o', 'u']
  
  WORD_LIST.filter fun word => 
    -- Check word length matches total vowels + consonants
    word.length = vowels + consonants ∧
    -- Check vowel count matches required number 
    (vowel_chars.map (countChar word) |>.foldl (·+·) 0) = vowels ∧
    -- Check no forbidden chars present
    !(forbidden.any fun c => word.toList.contains c)


theorem result_are_strings (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f → w.length ≥ 0 
  := by plausible
theorem exact_vowel_count (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f →
  (List.filter isVowel w.data).length = v
  := by plausible
theorem exact_total_length (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f →
  w.length = v + c
  := by plausible
theorem no_forbidden_chars (v c : Nat) (f : List Char) :
  ∀ (w : String), w ∈ wanted_words v c f →
  ∀ (x : Char), x ∈ f → ¬(x ∈ w.data)
  := by plausible
theorem all_forbidden_empty (v c : Nat) :
  wanted_words v c "abcdefghijklmnopqrstuvwxyz".data = []
  := by plausible