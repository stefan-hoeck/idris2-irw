module IRW.Algebra

import public IRW.Algebra.ZeroOneOmega
import public IRW.Algebra.Semiring
import public IRW.Algebra.Preorder

%default total

public export
RigCount : Type
RigCount = ZeroOneOmega

export
showCount : RigCount -> String
showCount = elimSemi "0 " "1 " (const "")
