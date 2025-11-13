import InfinityCosmos.BiCategoryTheory.SSetAlternative


open CategoryTheory

instance : @CategoryTheory.Limits.HasLimits SimplicialCategory.BiSSet _  := by
  unfold SimplicialCategory.BiSSet
