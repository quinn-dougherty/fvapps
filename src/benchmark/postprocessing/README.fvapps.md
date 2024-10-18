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

**BETA/DRAFT** Seeking funding or Anthropic credits to create more samples

## Example task

The goal is to remove every `sorry` but still make the lean executable happy.

Corresponding to [`APPS` problem id 23](https://huggingface.co/datasets/codeparrot/apps/viewer/all/train?row=23): 
```lean
def min_coins_for_votes (voters : List (Nat × Nat)) : Nat := sorry

theorem min_coins_for_votes_non_negative (voters : List (Nat × Nat)) :
  min_coins_for_votes voters ≥ 0 := sorry

theorem min_coins_for_votes_upper_bound (voters : List (Nat × Nat)) :
  min_coins_for_votes voters ≤ List.foldl (· + ·) 0 (List.map (λ p => p.2) voters) := sorry

theorem min_coins_for_votes_zero_votes (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.1 = 0) → min_coins_for_votes voters = 0 := sorry

theorem min_coins_for_votes_single_voter (v : Nat) (c : Nat) :
  min_coins_for_votes [(v, c)] = if v = 0 then 0 else c := sorry

theorem min_coins_for_votes_unit_cost (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.2 = 1) →
  min_coins_for_votes voters ≤ List.length voters ∧
  min_coins_for_votes voters ≤ List.foldl Nat.max 0 (List.map (λ p => p.1) voters) := sorry

theorem min_coins_for_votes_sorted_input (voters : List (Nat × Nat)) :
  min_coins_for_votes voters = min_coins_for_votes (List.map id voters) := sorry

theorem min_coins_for_votes_no_votes_needed (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.1 = 0) → min_coins_for_votes voters = 0 := sorry

theorem min_coins_for_votes_zero_cost (voters : List (Nat × Nat)) :
  (∀ v ∈ voters, v.2 = 0) → min_coins_for_votes voters = 0 := sorry
```
