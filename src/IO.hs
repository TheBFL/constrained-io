{-#LANGUAGE
    Safe,
    ExplicitNamespaces,
    TypeData,
    DataKinds,
    UndecidableInstances,
    AllowAmbiguousTypes,
    NoMonomorphismRestriction
#-}

module IO where
import Core

type data ConsoleCapability = ReadConsole | WriteConsole
instance Capability ConsoleCapability

type data FileCapability = OpenFile | ReadFile | WriteFile
instance Capability FileCapability

data IOModule = IOModuleKey

putStr = require @'[Allow WriteConsole]
    . performWith IOModuleKey
    . Prelude.putStr

putStrLn = require @'[Allow WriteConsole]
    . performWith IOModuleKey
    . Prelude.putStrLn


getLine = require @'[Allow ReadConsole]
    $ performWith IOModuleKey
    $ Prelude.getLine

readLn = require @'[Allow ReadConsole]
    $ performWith IOModuleKey
    $ Prelude.readLn

