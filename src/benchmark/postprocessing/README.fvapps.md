---
language: 
- en
pretty_name: "Formally Verified APPS"
tags:
- lean
- lean4
- software_engineering
- proof
- verification
---
# Formally Verified APPS

by Ronak Mehta and Quinn Dougherty. Based on APPS by Hendrycks et al.

**BETA/DRAFT** 

## Example task

The goal is to remove every `sorry` but still make the lean executable happy.

Corresponding to [`APPS` problem id 23](https://huggingface.co/datasets/codeparrot/apps/viewer/all/train?row=23): 
```lean
/--
Now elections are held in Berland and you want to win them. More precisely, you want everyone to vote for you.

There are $n$ voters, and two ways to convince each of them to vote for you. The first way to convince the $i$-th voter is to pay him $p_i$ coins. The second way is to make $m_i$ other voters vote for you, and the $i$-th voter will vote for free.

Moreover, the process of such voting takes place in several steps. For example, if there are five voters with $m_1 = 1$, $m_2 = 2$, $m_3 = 2$, $m_4 = 4$, $m_5 = 5$, then you can buy the vote of the fifth voter, and eventually everyone will vote for you. Set of people voting for you will change as follows: ${5} \rightarrow {1, 5} \rightarrow {1, 2, 3, 5} \rightarrow {1, 2, 3, 4, 5}$.

Calculate the minimum number of coins you have to spend so that everyone votes for you.
-/
def solve_elections (n : Nat) (voters : List (Nat × Nat)) : Nat := sorry

theorem solve_elections_nonnegative (n : Nat) (voters : List (Nat × Nat)) : solve_elections n voters ≥ 0 := sorry

theorem solve_elections_upper_bound (n : Nat) (voters : List (Nat × Nat)) : solve_elections n voters ≤ List.foldl (λ acc (pair : Nat × Nat) => acc + pair.2) 0 voters := sorry

theorem solve_elections_zero_votes (n : Nat) (voters : List (Nat × Nat)) : (List.all voters (λ pair => pair.1 = 0)) → solve_elections n voters = 0 := sorry

theorem solve_elections_single_zero_vote : solve_elections 1 [(0, 5)] = 0 := sorry
```

## Code to generate benchmark and baselines

[GitHub](https://github.com/quinn-dougherty/fvapps)
