theorem Tree.forall_insert_of_forall
        (h₁ : ForallTree p t) (h₂ : p key value)
        : ForallTree p (t.insert key value) := by
  induction h₁ with
  | leaf => exact .node .leaf h₂ .leaf
  | node hl hp hr ihl ihr =>
    rename Nat => k
    by_cases' key < k
    . exact .node ihl hp hr
    . by_cases' k < key
      . exact .node hl hp ihr
      . have_eq key k
        exact .node hl h₂ hr

theorem Tree.bst_insert_of_bst
        {t : Tree β} (h : BST t) (key : Nat) (value : β)
        : BST (t.insert key value) := by
  induction h with
  | leaf => exact .node .leaf .leaf .leaf .leaf
  | node h₁ h₂ b₁ b₂ ih₁ ih₂ =>
    rename Nat => k
    simp
    by_cases' key < k
    . exact .node (forall_insert_of_forall h₁ ‹key < k›) h₂ ih₁ b₂
    . by_cases' k < key
      . exact .node h₁ (forall_insert_of_forall h₂ ‹k < key›) b₁ ih₂
      . have_eq key k
        exact .node h₁ h₂ b₁ b₂

-- ...

theorem BinTree.find_mk (k : Nat)
        : BinTree.mk.find? k = (none : Option β) := by
  simp

theorem BinTree.find_insert (b : BinTree β) (k : Nat) (v : β)
        : (b.insert k v).find? k = some v := by
  let ⟨t, h⟩ := b; simp
  induction t with simp
  | node left key value right ihl ihr =>
    by_cases' k < key
    . cases h; apply ihl; assumption
    . by_cases' key < k
      cases h; apply ihr; assumption

theorem BinTree.find_insert_of_ne (b : BinTree β) (ne : k ≠ k') (v : β)
        : (b.insert k v).find? k' = b.find? k' := by
  let ⟨t, h⟩ := b; simp
  induction t with simp
  | leaf =>
    intros le
    exact Nat.lt_of_le_of_ne le ne
  | node left key value right ihl ihr =>
    let .node hl hr bl br := h
    specialize ihl bl
    specialize ihr br
    by_cases' k < key; by_cases' key < k
    have_eq key k
    by_cases' k' < k; by_cases' k  < k'
    have_eq k k'
    contradiction
