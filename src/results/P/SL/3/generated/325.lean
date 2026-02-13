

theorem closure_diff_closure_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) \ closure (B : Set X) ⊆ closure ((A \ B) : Set X) := by
  intro x hx
  rcases hx with ⟨hClA, hNotClB⟩
  -- We prove that `x` lies in the closure of `A \ B`.
  apply (mem_closure_iff).2
  intro U hUopen hxU
  -- Consider the open neighbourhood `U ∩ (closure B)ᶜ` of `x`,
  -- which is disjoint from `B`.
  let V : Set X := U ∩ (closure (B : Set X))ᶜ
  have hVopen : IsOpen V := hUopen.inter (isClosed_closure.isOpen_compl)
  have hxV : (x : X) ∈ V := And.intro hxU hNotClB
  -- Since `x ∈ closure A`, this open set meets `A`.
  obtain ⟨y, ⟨hyU, hyComplB⟩, hyA⟩ :=
    (mem_closure_iff).1 hClA V hVopen hxV
  -- The point `y` is in `U`, in `A`, and not in `B`.
  have hyNotB : (y : X) ∉ (B : Set X) := by
    intro hYB
    have : (y : X) ∈ closure (B : Set X) := subset_closure hYB
    exact hyComplB this
  -- Hence `y` witnesses that `U` meets `A \ B`.
  exact ⟨y, And.intro hyU (And.intro hyA hyNotB)⟩