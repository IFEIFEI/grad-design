
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}

module TypeLogic where

data HTrue
data HFalse
data HLTrue
data HRTrue

type family And f g where
    And HTrue HTrue = HTrue
    And HFalse _ = HFalse
    And _ HFalse = HFalse

type family Or f g where
    Or HTrue _ = HLTrue
    Or _ HTrue = HRTrue
    Or HFalse HFalse = HFalse

type family CastHTrue a where
    CastHTrue HFalse = HFalse
    CastHTrue HTrue = HTrue
    CastHTrue HLTrue = HTrue
    CastHTrue HRTrue = HTrue
