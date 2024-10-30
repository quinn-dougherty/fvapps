---
language: 
- en
pretty_name: "Formally Verified APPS"
tags:
- lean
- lean4
- software_engineering
---
# Formally Verified APPS

by Ronak Mehta and Quinn Dougherty. Based on APPS by Hendrycks et al.

**BETA/DRAFT** 

## Example task

The goal is to remove every `sorry` but still make the lean executable happy.

Corresponding to [`APPS` problem id 23](https://huggingface.co/datasets/codeparrot/apps/viewer/all/train?row=23): 
```lean
def solve_elections (n : Nat) (voters : List (Nat × Nat)) : Nat := sorry

theorem solve_elections_nonnegative (n : Nat) (voters : List (Nat × Nat)) : solve_elections n voters ≥ 0 := sorry

theorem solve_elections_upper_bound (n : Nat) (voters : List (Nat × Nat)) : solve_elections n voters ≤ List.foldl (λ acc (pair : Nat × Nat) => acc + pair.2) 0 voters := sorry

theorem solve_elections_zero_votes (n : Nat) (voters : List (Nat × Nat)) : (List.all voters (λ pair => pair.1 = 0)) → solve_elections n voters = 0 := sorry

theorem solve_elections_single_zero_vote : solve_elections 1 [(0, 5)] = 0 := sorry
```

## [Code to generate benchmark and baselines](https://github.com/quinn-dougherty/fvapps)
