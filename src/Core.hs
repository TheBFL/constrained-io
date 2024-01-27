{-#LANGUAGE
   ExplicitNamespaces,
   TypeData,
   Trustworthy,
   DataKinds,
   RoleAnnotations,
   TypeFamilies,
   UndecidableInstances,
   AllowAmbiguousTypes,
   GeneralizedNewtypeDeriving
#-}
module Core ( 
    Constrained (),
    Permission (Allow),
    DevolvedPermission (Grant),
    Capability,
    HasPermissions,
    HasGrantedPermissions,
    require,
    run,
    restrict,
    perform,
    withGrantedPermissions,
    performWith,
    CoreCapability (PerformAny)
) where

import Data.Kind
import Data.Coerce
import GHC.TypeLits
import GHC.TypeError
import Data.Type.Equality (type (==))


type Constrained :: (Type -> Type) -> Reducible -> [DevolvedPermission] -> [Permission] -> Type -> Type
type role Constrained nominal nominal nominal nominal nominal
newtype Constrained m r devpl avpl a where
    MkConstrained :: m a -> Constrained m r devpl avpl a
    deriving (
        Functor,
        Applicative,
        Monad, 
        MonadFail,
        Semigroup,
        Monoid
    )

type CIO = Constrained IO

type data Permission where
    Allow :: forall k. k -> Permission

type data DevolvedPermission where
    Grant :: Type -> [Permission] -> DevolvedPermission

class Capability k where
    type AllowedBy (x :: k) (y :: k) :: Bool
    type AllowedBy x y = x == y

type data CoreCapability = PerformAny (Type -> Type)

require :: forall
    {m :: Type -> Type}
    {r :: Reducible}
    {devpl :: [DevolvedPermission]}
    {avpl :: [Permission]}
    (reqpl :: [Permission])
    (a :: Type).
    HasPermissions r reqpl avpl
    => Constrained m r devpl avpl a
    -> Constrained m r devpl avpl a
require = id


run :: forall
    (devpl :: [DevolvedPermission])
    (avpl :: [Permission])
    (a :: Type).
    Constrained IO SReducible devpl avpl a
    -> IO a
run = coerce


restrict :: forall
    {m :: Type -> Type}
    {r :: Reducible}
    {devpl :: [DevolvedPermission]}
    {avpl :: [Permission]}
    (new_pl :: [Permission])
    (a :: Type).
    HasPermissions r new_pl avpl
    => Constrained m r devpl new_pl a
    -> Constrained m r devpl avpl a
restrict = coerce 


perform :: forall
    {m :: Type -> Type}
    {r :: Reducible}
    {devpl :: [DevolvedPermission]}
    {avpl :: [Permission]}
    (a :: Type).
    HasPermissions r '[Allow (PerformAny m)] avpl
    => m a
    -> Constrained m r devpl avpl a
perform = MkConstrained


withGrantedPermissions :: forall
    {m :: Type -> Type}
    {r :: Reducible}
    {devpl :: [DevolvedPermission]}
    {avpl :: [Permission]}
    {key :: Type}
    (using :: [Permission])
    (a :: Type). 
    HasGrantedPermissions r using key devpl
    => key 
    -> Constrained m r devpl (Join r using avpl) a
    -> Constrained m r devpl avpl a
withGrantedPermissions key = coerce . seq key 


performWith :: forall
    {m :: Type -> Type}
    {r :: Reducible}
    {devpl :: [DevolvedPermission]}
    {avpl :: [Permission]}
    {key :: Type}
    (a :: Type).
    HasGrantedPermissions r '[Allow (PerformAny m)] key devpl
    => key
    -> m a
    -> Constrained m r devpl avpl a
performWith key = coerce . seq key
--performWith keyvalue (action :: m a) = withGrantedPermissions @'[Allow (PerformAny m)] keyvalue $ perform action






type data Reducible = SReducible



type CheckAllowedBy :: Permission -> Permission -> Bool
type family CheckAllowedBy a b where
    CheckAllowedBy (Allow @k x) (Allow @k y) = AllowedBy x y
    CheckAllowedBy _ _ = False


type PermissionListAllows :: Permission -> [Permission] -> Bool
type family PermissionListAllows reqp avpl where
    PermissionListAllows _ '[] = False
    PermissionListAllows req (x:xs) = CheckAllowedBy req x || PermissionListAllows req xs


type PermissionsNotAllowedBy :: [Permission] -> [Permission] -> [Permission]
type family PermissionsNotAllowedBy reqpl avpl where
    PermissionsNotAllowedBy '[] _ = '[]
    PermissionsNotAllowedBy (x:xs) avpl = If (PermissionListAllows x avpl)
        (PermissionsNotAllowedBy xs avpl)
        (x : PermissionsNotAllowedBy xs avpl)


type AssertPermissionListEmpty :: ErrorMessage -> [Permission] -> Constraint
type family AssertPermissionListEmpty msgPrefix dapl where
    AssertPermissionListEmpty _ '[] = ()
    AssertPermissionListEmpty msgPrefix dapl = Unsatisfiable (
            msgPrefix
            :$$: BuildErrorMessage dapl
        )

type BuildErrorMessage:: [Permission] -> ErrorMessage
type family BuildErrorMessage pl where
    BuildErrorMessage '[Allow p] = ShowType p
    BuildErrorMessage (Allow p:xs) = ShowType p :<>: Text ", " :<>: BuildErrorMessage xs


type HasPermissions :: Reducible -> [Permission] -> [Permission] -> Constraint
type family HasPermissions r reqpl avpl where
    HasPermissions SReducible reqpl avpl = AssertPermissionListEmpty 
        (Text "Permissions required but not given:")
        (PermissionsNotAllowedBy reqpl avpl)


type Join :: Reducible -> [Permission] -> [Permission] -> [Permission]
type family Join r a b where
    Join SReducible a b = Append (PermissionsNotAllowedBy a b) (PermissionsNotAllowedBy b a) 


type RemainingPermissionsAfterGranting :: [Permission] -> Type -> [DevolvedPermission] -> [Permission]
type family RemainingPermissionsAfterGranting reqpl key devpl where
    RemainingPermissionsAfterGranting reqpl _ '[] = reqpl
    RemainingPermissionsAfterGranting reqpl key (Grant key pl:xs) = RemainingPermissionsAfterGranting 
        (PermissionsNotAllowedBy reqpl pl) key xs
    RemainingPermissionsAfterGranting reqpl key (_:xs) = RemainingPermissionsAfterGranting reqpl key xs


type HasGrantedPermissions :: Reducible -> [Permission] -> Type -> [DevolvedPermission] -> Constraint
type family HasGrantedPermissions r reqpl key devpl where
    HasGrantedPermissions SReducible reqpl key devpl = AssertPermissionListEmpty
        (Text "Permissions expected, but not granted to key " :<>: ShowType key :<>: Text ":")
        (RemainingPermissionsAfterGranting reqpl key devpl)


type If :: forall k. Bool -> k -> k -> k
type family If cond a b where
    If True a b = a
    If False a b = b

type (||) :: Bool -> Bool -> Bool
type family (||) a b where
    True || _ = True
    False || x = x

type Append :: forall a. [a] -> [a] -> [a]
type family Append a b where
    Append '[] rest = rest
    Append (x:xs) rest = x : Append xs rest

