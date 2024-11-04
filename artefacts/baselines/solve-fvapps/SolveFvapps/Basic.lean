/- Basic definitions and helper functions for the fusion verification conditions solver -/

import Lean.Meta
import Std
import Mathlib.Data.List.Basic

open Lean Meta Expr

/-- Convert an fvar id to a string for use as map keys -/
def fvarIdToString (fid: FVarId): String :=
  toString fid.name

/-- Helper for printing expressions with context -/
def printExpr (e: Expr) (indent: String := "") : MetaM String := do
  let fmt ← ppExpr e
  return s!"{indent}{fmt}"

/-- Type to represent the current state of solving fvapps equations -/
structure FvappsState where
  /-- Map from free var id to its substituted expression -/
  fvarMap : Std.HashMap String Expr := Std.HashMap.empty
  /-- Set of equations we have processed -/ 
  processed : Std.HashSet String := Std.HashSet.empty
  deriving Inhabited

/-- Extract the FVarId from an Expr assumed to be a free variable -/
def getFVarId (e: Expr) : MetaM FVarId := do
  match e with
  | .fvar fid => return fid
  | _ => throwError "Expected free variable but got {← ppExpr e}"

/-- Check if an expression is a free variable -/
def checkIsFVar (e: Expr) : Bool :=
  match e with
  | .fvar _ => true
  | _ => false

/-- Get a short string key for an equation to track processed state -/
def getEqKey (lhs rhs: Expr) : String :=
  s!"{lhs.hash}={rhs.hash}"

/-- Convert a number to a hex digit (0-f) -/
def digitToHex (n : Nat) : Char :=
  if n < 10 then 
    Char.ofNat (n + '0'.toNat)
  else
    Char.ofNat (n - 10 + 'a'.toNat)

/-- Convert a Nat to hex string using recursion -/
def to_hex_rec (n : Nat) (acc : List Char) : List Char :=
  if n = 0 then 
    if acc.length = 0 then ['0'] else acc
  else
    to_hex_rec (n / 16) (digitToHex (n % 16) :: acc)

def to_hex (n : Nat) : String := String.mk (to_hex_rec n [])

/-- Convert a hex string back to Nat -/
def hexToNat (s : String) : Nat :=
  s.data.foldl (fun acc c =>
    let digit := 
      if ('0' ≤ c && c ≤ '9') then
        c.toNat - '0'.toNat
      else 
        c.toNat - 'a'.toNat + 10
    acc * 16 + digit
  ) 0

/-- Main function to solve fvapp verification conditions.
    Returns updated substitution map and flag indicating if progress was made. -/
def solveFvapps (eqns: Array (Expr × Expr)) (state: FvappsState) : 
  MetaM (FvappsState × Bool) := do
  let mut newState := state
  let mut madeProgress := false

  -- Try to solve each equation
  for (lhs, rhs) in eqns do
    let key := getEqKey lhs rhs
    -- Skip if already processed
    if state.processed.contains key then continue

    -- Try substituting existing mappings
    let lhs' ← instantiateMVars lhs
    let rhs' ← instantiateMVars rhs

    if checkIsFVar lhs' then
      let fid ← getFVarId lhs'
      let fidStr := fvarIdToString fid
      newState := { 
        newState with
        fvarMap := newState.fvarMap.insert fidStr rhs',
        processed := newState.processed.insert key
      }
      madeProgress := true
    else if checkIsFVar rhs' then
      let fid ← getFVarId rhs'
      let fidStr := fvarIdToString fid
      newState := {
        newState with
        fvarMap := newState.fvarMap.insert fidStr lhs',
        processed := newState.processed.insert key
      }
      madeProgress := true

  return (newState, madeProgress)

theorem digit_valid_range (n : Nat) (h : n < 16) : 
  let c := digitToHex n
  if n < 10 then
    c.toNat = n + '0'.toNat
  else 
    c.toNat = n - 10 + 'a'.toNat := by
  simp [digitToHex]
  by_cases h₁ : n < 10
  . simp [h₁]
  . simp [h₁] 

theorem to_hex_positive_integers (n : Nat) (h : n < 2^32) : 
  let result := to_hex n
  (hexToNat result = n) ∧ 
  (result.length ≤ 8) ∧
  (∀ c ∈ result.data, c.toNat < 128) := by
  simp [to_hex]
  by_cases h0 : n = 0
  . -- Case n = 0 
    simp [h0, to_hex_rec]
    apply And.intro
    . -- hexToNat "0" = 0
      simp [hexToNat]
      rfl
    apply And.intro
    . -- length "0" ≤ 8
      exact Nat.le_refl 1
    . -- All chars are ASCII
      intros c hc
      simp at hc
      simp [hc]
      decide
  . -- Case n ≠ 0
    sorry