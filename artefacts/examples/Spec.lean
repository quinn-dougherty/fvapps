def maxChar (s : String) : Char :=
  sorry

theorem max_char_in_string (s : String) (h : s.length > 0) :
  (maxChar s) ∈ s.data ∧
  ∀ c ∈ s.data, (s.data.count (maxChar s)) ≥ (s.data.count c) :=
sorry

theorem max_char_consistent (s : String) (h : s.length > 0) :
  maxChar s = maxChar s :=
sorry

theorem max_char_concatenation (s1 s2 : String) (h1 : s1.length > 0) (h2 : s2.length > 0) :
  let result := maxChar (s1 ++ s2)
  (result ∈ s1.data ∨ result ∈ s2.data) ∧
  (s1.data.count result + s2.data.count result =
   List.maximum ((s1 ++ s2).data.map (fun c => s1.data.count c + s2.data.count c))) :=
sorry

theorem max_char_reverse (s : String) (h : s.length > 0) :
  s.data.count (maxChar s) = s.data.reverse.count (maxChar (String.mk s.data.reverse)) :=
sorry

theorem max_char_specific_cases :
  (maxChar "aaa" = 'a') ∧
  (maxChar "abcabc" = 'a') ∧
  (maxChar " " = ' ') :=
sorry

theorem max_char_empty_string_error :
  ∀ s : String, s.length = 0 → ¬∃ c, maxChar s = c :=
sorry

theorem max_char_lowercase (s : String) (h : s.length > 0)
  (h_lowercase : ∀ c ∈ s.data, c.isLower) :
  (maxChar s).isLower :=
sorry

theorem max_char_digits (s : String) (h : s.length > 0)
  (h_digits : ∀ c ∈ s.data, c.isDigit) :
  (maxChar s).isDigit :=
sorry

theorem max_char_not_unique (s : String) (h : s.length > 1) :
  (s.data.count (maxChar s) > 1) ∨ (s.data.eraseDups.length = s.length) :=
sorry