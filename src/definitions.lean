import data.finset

universes u

open finset

variables {α : Type u} [decidable_eq α] -- need decidability for set difference

def independent (ℐ : finset (finset α)) (I₁ I₂ : finset α) (h₁ : I₁ ∈ ℐ) (h₂ : I₂ ∈ ℐ) : Prop := 
  finset.card I₁ < finset.card I₂ →  ∃ (e ∈ I₂ \ I₁), (insert e I₁ ∈ ℐ)

def independent_collection (ℐ : finset (finset α)) : Prop := 
  ∀ (I₁ I₂ : finset α) (h₁ : I₁ ∈ ℐ) (h₂ : I₂ ∈ ℐ), independent ℐ I₁ I₂ h₁ h₂
-- don't love that

/- A matroid M is an ordered pair `(E, ℐ)` consisting of a finite set `E` and 
a collection `ℐ` of subsets of `E` having the following three properties:
  (I1) `∅ ∈ ℐ`.
  (I2) If `I ∈ ℐ` and `I' ⊆ I`, then `I' ∈ ℐ`.
  (I3) If `I₁` and `I₂` are in `I` and `|I₁| < |I₂|`, then there is an element `e` of `I₂ − I₁`
    such that `I₁ ∪ {e} ∈ I`.-/
structure matroid (E : finset α) (ℐ : finset (finset α)) :=
(subsets : ∀ (I ∈ ℐ), I ⊆ E)
(empty : ∅ ∈ ℐ)
(hereditary : ∀ (I₁ ∈ ℐ), ∀ (I₂ : finset α), I₂ ⊆ I₁ → I₂ ∈ ℐ)
(ind : independent_collection ℐ)


/- A subset of `E` that is not in `ℐ` is called dependent. -/ 
-- is this something that merits a separate definition?
def dependent_sets (E : finset α) (ℐ : finset (finset α)) : finset (finset α) := E.powerset \ ℐ

variables {E : finset α} {ℐ : finset (finset α)}
variables [decidable_pred (λ (D : finset α), independent_collection (erase D.powerset D))]
-- figure out where this needs to go later

namespace matroid

def circuit (M : matroid E ℐ) : finset (finset α) :=
  filter (λ (D : finset α), independent_collection (erase D.powerset D)) (dependent_sets E ℐ)

-- we're not defining n-circuits lmao

/- `(C1)` ∅ ∉ C  -/
lemma empty_notmem_circuit (M : matroid E ℐ) : ∅ ∉ M.circuit := 
begin
  -- this is just due to the fact that ∅ ∈ ℐ lol
  unfold matroid.circuit,
  unfold dependent_sets,
  rw mem_filter,
  rw and_comm,
  push_neg,
  intros h,
  simp,
  exact M.empty,
end

/- `(C2)` if C₁ and C₂ are members of C and C₁ ⊆ C₂, then C₂ = C₂. 
In other words, C forms an antichain. -/
lemma circuit_antichain (M : matroid E ℐ) (C₁ C₂ : finset α) (h₁ : C₁ ∈ M.circuit) (h₂ : C₂ ∈ M.circuit) :
  C₁ ⊆ C₂ → C₁ = C₂ :=
begin
  intros h,
  sorry,
end

end matroid