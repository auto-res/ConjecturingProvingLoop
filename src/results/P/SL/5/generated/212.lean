

theorem closure_inter_interior_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxCl, hxInt⟩
    rcases mem_interior.1 hxInt with ⟨U, hUsub, hUopen, hxU⟩
    have hNon : ((U : Set X) ∩ (A : Set X)).Nonempty := by
      have hClosure := (mem_closure_iff).1 hxCl
      exact hClosure U hUopen hxU
    rcases hNon with ⟨y, ⟨hyU, hyA⟩⟩
    have hyCompl : y ∈ ((A : Set X)ᶜ) := hUsub hyU
    have : False := hyCompl hyA
    exact this.elim
  · intro hx
    cases hx