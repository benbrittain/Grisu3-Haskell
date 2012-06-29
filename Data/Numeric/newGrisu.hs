import Data.Bits
--import CachedPowers
import GHC.Int
import Data.Maybe
import Debug.Trace


normFloat (diyfp,_,_) = diyfp

formatFloat :: RealFloat a => a -> (DiyFp, DiyFp, DiyFp)
formatFloat input   = (w,wPlus,wMinus)
    where   v       =   createDiyFp (fst $ decodeFloat(input)) (fromIntegral (snd $ decodeFloat(input)))
            w       =   normalize v
            wPlus   =   normalize $ createDiyFp (((f v) `shiftL` 1) + 1) ((e v) -1) 
            mMinus  =   if (f v == kHiddenBit) && (e v /= kDenormalExponent)
                            then createDiyFp ((f v `shiftL` 2) - 1) (e v - 2)
                            else createDiyFp ((f v `shiftL` 1) - 1) (e v - 1)
                                where   kHiddenBit = 2^52
                                        kSignificandSize = 52
                                        kExponentBias = 0x3FF + kSignificandSize
                                        kDenormalExponent = -kExponentBias + 1
            wMinus  =   createDiyFp ((f mMinus) `shiftL` fromIntegral (e mMinus - e wPlus)) (e wPlus)
            
            assert  = (e wPlus) == (e w)

scale:: (DiyFp, DiyFp, DiyFp) -> (DiyFp, DiyFp, DiyFp)
scale (w,wPlus,wMinus) = (sw, swp, swn)
    where   sw      = w * (frexp10 w)
            swp     = wPlus * (frexp10 w)
            swn     = wMinus * ( frexp10 w)
--   ASSERT(scaled_w.e() ==  boundary_plus.e() + ten_mk.e() + DiyFp::kSignificandSize); valid

normalize :: DiyFp -> DiyFp
normalize v
            | f v                   == 0 = v
            | f v < (1 `shiftL` 55)      = normalize (createDiyFp ((f v) `shiftL` 8) ((e v) - 8))
            | (f v) .&. (2^63) == 0      = normalize (createDiyFp ((f v) `shiftL` 1) ((e v) - 1))
            | otherwise                  = v


minExp = -60
maxExp = -32

frexp10 fp              = powersOfTen !! index
    where   expTen      = floor ((-1 * ((fromIntegral (e fp)) + 100)) * (1/(logBase 2 10)))
            i           = floor $ (fromIntegral (expTen - firstPowerOfTen))/ (fromIntegral stepPowerOfTen)
            (exp,index) = fakeLoop i ((e fp) + (e (powersOfTen !! i)) + 64) fp

fakeLoop i exp f
    | exp < minExp = fakeLoop (i+1) ((e f) + (e (powersOfTen !! i)) + 64) f
    | exp > maxExp = fakeLoop (i - 1) ((e f) + (e (powersOfTen !! i)) + 64) f
    | otherwise    = (firstPowerOfTen + (((fromIntegral i)* (fromIntegral stepPowerOfTen))), i)

--digitGen :: (DiyFp, DiyFp, DiyFp) -> [Integer]
digitGen (fp,high,low)      = finalFormat (kappa,pointless, de)
    where   too_low         = createDiyFp ((f low) - 1) (e low)
            too_high        = createDiyFp ((f high) + 1) (e high)
            unsafe_int      = too_high - too_low
            shift           = fromIntegral (-1 * (e fp))
            one             = createDiyFp (1 `shiftL` shift) (e fp)
            integrals       = (f too_high) `shiftR` shift
            fractional      = (f too_high) .&. ((f one) -1)
            rest            = (integrals `shiftL` shift) + fractional
            (divider, de)   = powerTen integrals (kSignificandSize - (-1 * (e one)))
            (kappa,pointless)= calcInvariant (de + 1) "" integrals divider fractional shift too_high fp unsafe_int one 0 1

finalFormat (kappa, (Just x), de) = (-de + kappa, x)
            
calcInvariant kappa buffer integrals divider fractional shift too_high fp unsafe one length unit
    | (kappa > 0) && (rest < (f unsafe))    = (kappa, roundWeed (buffer ++ (show digit)) length (f (too_high - fp)) (f unsafe) rest (divider `shiftL` shift) unit)
    | (kappa > 0)                           = calcInvariant (kappa - 1) (buffer ++ (show digit)) (integrals `mod` divider) (divider `div` 10) fractional shift too_high fp unsafe one (length + 1) unit
    | (((fractional * 5) .&. (f one `shiftR` 1) - 1) < (f unsafe * 5)) = (kappa, roundWeed (buffer ++ show ((fractional*5) `shiftR` shift)) (length + 1) (f (too_high - fp)) (f unsafe * 5) (fractional * 5) (f one `shiftR` 1) (unit*5))
    | otherwise                             = calcInvariant (kappa - 1) (buffer ++ show ((fractional*5) `shiftR` shift)) integrals divider ((fractional * 5) .&. (f one `shiftR` 1) - 1) shift too_high fp (createDiyFp (f unsafe * 4) (e unsafe + 1)) (createDiyFp (f one `shiftR` 1) (e one + 1)) (length + 1) (unit * 5)
        where   rest = ((integrals `mod` divider) `shiftL` shift) + fractional
                digit = integrals `div` divider

kSignificandSize = 64

roundWeed buffer length distanceHigh unsafe rest tenkappa unit
    | ((rest < smallDistance) && (unsafe - rest >= tenkappa)) && ((rest + tenkappa) < smallDistance) || (smallDistance - rest >= rest + tenkappa - smallDistance) = trace ("kappa" ++ show tenkappa ++ " buffer " ++ (show buffer)) roundWeed (init buffer ++ [pred (last buffer)]) length distanceHigh unsafe (rest + tenkappa) tenkappa unit
    | otherwise =   if  ((rest < bigDistance) && (unsafe - rest) >= tenkappa) && ((rest + tenkappa < bigDistance) || (bigDistance - rest) > (rest + tenkappa - bigDistance))
                    then Nothing
                    else    if ((2 * unit) <= rest) && (rest <= unsafe - (4 * unit))
                            then Just buffer
                            else Nothing
    where smallDistance = distanceHigh - 1
          bigDistance = distanceHigh + 1

powerTen :: (Num a, Num t1, Num t2, Ord a) => t -> a -> (t1, t2)
powerTen number bits
    | (bits >= 30 && bits <= 32) = (1000000000,9)
    | bits >= 27 = (100000000,8)
    | bits >= 24 = (10000000,7)
    | bits >= 20 = (1000000,6)
    | bits >= 17 = (100000,5)
    | bits >= 14 = (10000,4)
    | bits >= 10 = (1000,3)
    | bits >= 7  = (100,2)
    | bits >= 4  = (10,1)
    | bits >= 1  = (1,0)
    | bits == 0  = (0,(-1))
    | otherwise  = (0,0)


instance Num DiyFp where
    (+)     x y = addDiyFp x y
    (-)     x y = subDiyFp x y
    (*)     x y = mulDiyFp x y

addDiyFp    x y =   createDiyFp ((f x) + (f y)) (e x) 
subDiyFp    x y =   createDiyFp ((f x) - (f y)) (e x)

mulDiyFp   x y = result
                where   a = (f x) `shiftR` 32
                        b = (f x) .&. 0xFFFFFFFF 
                        c = (f y) `shiftR` 32
                        d = (f y) .&. 0xFFFFFFFF
                        tmp = ((((b*d) `shiftR` 32) + ((a*d) .&. 0xFFFFFFFF) + ((b*c) .&. 0xFFFFFFFF)) + (1 `shiftL` 31))
                        newF = (a*c) + ((a*d) `shiftR` 32) + ((b*c) `shiftR` 32) + (tmp `shiftR` 32)
                        newE  = ((e x) + (e y) + 64) 
                        result = createDiyFp newF newE

createDiyFp :: Integer -> Int16 -> DiyFp
createDiyFp x y = DiyFp x y

data DiyFp = DiyFp  { f :: Integer
                    , e :: Int16
                    }
    deriving(Show)


firstPowerOfTen = -348
stepPowerOfTen  = 8

powersOfTen = [ 
	(DiyFp 0xfa8fd5a0081c0288 (-1220)),
	(DiyFp 0xbaaee17fa23ebf76 (-1193)),
	(DiyFp 0x8b16fb203055ac76 (-1166)),
	(DiyFp 0xcf42894a5dce35ea (-1140)),
	(DiyFp 0x9a6bb0aa55653b2d (-1113)),
	(DiyFp 0xe61acf033d1a45df (-1087)),
	(DiyFp 0xab70fe17c79ac6ca (-1060)),
	(DiyFp 0xff77b1fcbebcdc4f (-1034)),
	(DiyFp 0xbe5691ef416bd60c (-1007)),
	(DiyFp 0x8dd01fad907ffc3c (-980)),
	(DiyFp 0xd3515c2831559a83 (-954)),
	(DiyFp 0x9d71ac8fada6c9b5 (-927)),
	(DiyFp 0xea9c227723ee8bcb (-901)),
	(DiyFp 0xaecc49914078536d (-874)),
	(DiyFp 0x823c12795db6ce57 (-847)),
	(DiyFp 0xc21094364dfb5637 (-821)),
	(DiyFp 0x9096ea6f3848984f (-794)),
	(DiyFp 0xd77485cb25823ac7 (-768)),
	(DiyFp 0xa086cfcd97bf97f4 (-741)),
	(DiyFp 0xef340a98172aace5 (-715)),
	(DiyFp 0xb23867fb2a35b28e (-688)),
	(DiyFp 0x84c8d4dfd2c63f3b (-661)),
	(DiyFp 0xc5dd44271ad3cdba (-635)),
	(DiyFp 0x936b9fcebb25c996 (-608)),
	(DiyFp 0xdbac6c247d62a584 (-582)),
	(DiyFp 0xa3ab66580d5fdaf6 (-555)),
	(DiyFp 0xf3e2f893dec3f126 (-529)),
	(DiyFp 0xb5b5ada8aaff80b8 (-502)),
	(DiyFp 0x87625f056c7c4a8b (-475)),
	(DiyFp 0xc9bcff6034c13053 (-449)),
	(DiyFp 0x964e858c91ba2655 (-422)),
	(DiyFp 0xdff9772470297ebd (-396)),
	(DiyFp 0xa6dfbd9fb8e5b88f (-369)),
	(DiyFp 0xf8a95fcf88747d94 (-343)),
	(DiyFp 0xb94470938fa89bcf (-316)),
	(DiyFp 0x8a08f0f8bf0f156b (-289)),
	(DiyFp 0xcdb02555653131b6 (-263)),
	(DiyFp 0x993fe2c6d07b7fac (-236)),
	(DiyFp 0xe45c10c42a2b3b06 (-210)),
	(DiyFp 0xaa242499697392d3 (-183)),
	(DiyFp 0xfd87b5f28300ca0e (-157)),
	(DiyFp 0xbce5086492111aeb (-130)),
	(DiyFp 0x8cbccc096f5088cc (-103)),
	(DiyFp 0xd1b71758e219652c (-77)),
	(DiyFp 0x9c40000000000000 (-50)),
	(DiyFp 0xe8d4a51000000000 (-24)),
	(DiyFp 0xad78ebc5ac620000 (3) ),
	(DiyFp 0x813f3978f8940984 (30)),
	(DiyFp 0xc097ce7bc90715b3 (56)),
	(DiyFp 0x8f7e32ce7bea5c70 (83)),
	(DiyFp 0xd5d238a4abe98068 (109)),
	(DiyFp 0x9f4f2726179a2245 (136)),
	(DiyFp 0xed63a231d4c4fb27 (162)),
	(DiyFp 0xb0de65388cc8ada8 (189)),
	(DiyFp 0x83c7088e1aab65db (216)),
	(DiyFp 0xc45d1df942711d9a (242)),
	(DiyFp 0x924d692ca61be758 (269)),
	(DiyFp 0xda01ee641a708dea (295)),
	(DiyFp 0xa26da3999aef774a (322)),
	(DiyFp 0xf209787bb47d6b85 (348)),
	(DiyFp 0xb454e4a179dd1877 (375)),
	(DiyFp 0x865b86925b9bc5c2 (402)),
	(DiyFp 0xc83553c5c8965d3d (428)),
	(DiyFp 0x952ab45cfa97a0b3 (455)),
	(DiyFp 0xde469fbd99a05fe3 (481)),
	(DiyFp 0xa59bc234db398c25 (508)),
	(DiyFp 0xf6c69a72a3989f5c (534)),
	(DiyFp 0xb7dcbf5354e9bece (561)),
	(DiyFp 0x88fcf317f22241e2 (588)),
	(DiyFp 0xcc20ce9bd35c78a5 (614)),
	(DiyFp 0x98165af37b2153df (641)),
	(DiyFp 0xe2a0b5dc971f303a (667)),
	(DiyFp 0xa8d9d1535ce3b396 (694)),
	(DiyFp 0xfb9b7cd9a4a7443c (720)),
	(DiyFp 0xbb764c4ca7a44410 (747)),
	(DiyFp 0x8bab8eefb6409c1a (774)),
	(DiyFp 0xd01fef10a657842c (800)),
	(DiyFp 0x9b10a4e5e9913129 (827)),
	(DiyFp 0xe7109bfba19c0c9d (853)),
	(DiyFp 0xac2820d9623bf429 (880)),
	(DiyFp 0x80444b5e7aa7cf85 (907)),
	(DiyFp 0xbf21e44003acdd2d (933)),
	(DiyFp 0x8e679c2f5e44ff8f (960)),
	(DiyFp 0xd433179d9c8cb841 (986)),
	(DiyFp 0x9e19db92b4e31ba9 (1013)),
	(DiyFp 0xeb96bf6ebadf77d9 (1039)),
	(DiyFp 0xaf87023b9bf0ee6b (1066))]

