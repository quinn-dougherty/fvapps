dslkjf
def maxChar (message : String) : Char :=
  sorry

theorem maxChar_in_string (message : String) (h : message ≠ "") :
  maxChar message ∈ message.data :=
  sorry

theorem maxChar_max_count (message : String) (h : message ≠ "") :
  ∀ c ∈ message.data, message.data.count (maxChar message) ≥ message.data.count c :=
  sorry

theorem maxChar_singleton (c : Char) :
  maxChar (String.mk [c]) = c :=
  sorry

theorem maxChar_empty_string :
  ∀ (e : String), e = "" → (maxChar e : Option Char) = none :=
  sorry

theorem maxChar_lowercase (message : String) (h : message ≠ "") (h2 : ∀ c ∈ message.data, c.isLower) :
  (maxChar message).isLower :=
  sorry

theorem maxChar_uppercase (message : String) (h : message ≠ "") (h2 : ∀ c ∈ message.data, c.isUpper) :
  (maxChar message).isUpper :=
  sorry

theorem maxChar_digits (message : String) (h : message ≠ "") (h2 : ∀ c ∈ message.data, c.isDigit) :
  (maxChar message).isDigit :=
  sorry

theorem maxChar_punctuation (message : String) (h : message ≠ "") (h2 : ∀ c ∈ message.data, c.isAlphanum = false) :
  (maxChar message).isAlphanum = false :=
  sorry

theorem maxChar_repeated_char (s : String) (c : Char) (h : s ≠ "") :
  maxChar (s ++ String.mk (List.replicate (s.length + 1) c)) = c :=
  sorry

theorem maxChar_tie_breaker (message : String) (h : message ≠ "") :
  ∀ c ∈ message.data, message.data.count c = message.data.count (maxChar message) →
    message.data.indexOf c ≥ message.data.indexOf (maxChar message) :=
  sorry

theorem maxChar_first_occurrence (message : String) (h : message.length ≥ 2) :
  ∀ c ∈ message.data, c ≠ maxChar message →
    message.data.count c = message.data.count (maxChar message) →
    message.data.indexOf c > message.data.indexOf (maxChar message) :=
  sorry
