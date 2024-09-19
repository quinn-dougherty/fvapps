def max_char (message : String) : Char := sorry

theorem max_char_in_string (s : String) (h : s.length > 0) :
  (∃ c, c ∈ s.data ∧ max_char s = c) ∧
  (∀ c ∈ s.data, s.data.count (max_char s) ≥ s.data.count c) := sorry

theorem max_char_consistent (s : String) (h : s.length > 0) :
  max_char s = max_char s := sorry

theorem max_char_concatenation (s1 s2 : String) (h1 : s1.length > 0) (h2 : s2.length > 0) :
  (max_char (s1 ++ s2) ∈ s1.data ∨ max_char (s1 ++ s2) ∈ s2.data) ∧
  ((s1.data.count (max_char (s1 ++ s2))) + (s2.data.count (max_char (s1 ++ s2))) =
   (s1 ++ s2).data.foldl (λ acc c => max acc ((s1.data.count c) + (s2.data.count c))) 0) := sorry

theorem max_char_reverse (s : String) (h : s.length > 0) :
  s.data.count (max_char s) = s.data.reverse.count (max_char (String.mk s.data.reverse)) := sorry

theorem max_char_specific_cases :
  (max_char "aaa" = 'a') ∧
  (max_char "abcabc" = 'a') ∧
  (max_char " " = ' ') := sorry

theorem max_char_empty_string_error :
  (∀ s : String, s.length = 0 → max_char s = default) := sorry

theorem max_char_lowercase (s : String) (h : s.length > 0) 
  (h_lowercase : ∀ c ∈ s.data, c.isLower) :
  (max_char s).isLower := sorry

theorem max_char_digits (s : String) (h : s.length > 0)
  (h_digits : ∀ c ∈ s.data, c.isDigit) :
  (max_char s).isDigit := sorry

theorem max_char_not_unique (s : String) (h : s.length > 1) :
  s.data.count (max_char s) > 1 ∨ s.data.eraseDups.length = s.length := sorry