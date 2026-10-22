import Saw38a.Statements28f
import Saw38a.Final
import Saw38a.Fekete
/-! The final theorems have exactly the statements of `Statements28f.lean`. -/
example : type_of% @Saw38a.cert_exists = type_of% @Saw38a.K28F.cert_exists := rfl
example : type_of% @Saw38a.bridge_bound = type_of% @Saw38a.K28F.bridge_bound := rfl
example : type_of% @Saw38a.connective_constant_le = type_of% @Saw38a.K28F.connective_constant_le := rfl
example : type_of% @Saw38a.bridge_bound_of_cert = type_of% @Saw38a.bridge_bound_of_cert' := rfl
example : type_of% @Saw38a.connective_constant_exists = type_of% @Saw38a.connective_constant_exists' := rfl
example : type_of% @Saw38a.hw = type_of% @Saw38a.hw' := rfl
#print axioms Saw38a.K28F.connective_constant_le
#print axioms Saw38a.K28F.connective_constant_le_unconditional
#print axioms Saw38a.hw'
#print axioms Saw38a.K28F.bridge_bound
