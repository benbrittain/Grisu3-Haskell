import Data.Bits
--import CachedPowers
import GHC.Int
import Data.Maybe
import Debug.Trace


grisu3 input    = (buffer, (kappa + (-1*mk)))
    where   v               =   createDiyFp (fst $ decodeFloat(input)) (fromIntegral (snd $ decodeFloat(input)))
            w               =   normalize v
            boundryPlus     =   normalize $ createDiyFp (((f v) `shiftL` 1) + 1) ((e v) -1) 
            mMinus          =   if (f v == kHiddenBit) && (e v /= kDenormalExponent)
                                then createDiyFp ((f v `shiftL` 2) - 1) (e v - 2)
                                else createDiyFp ((f v `shiftL` 1) - 1) (e v - 1)
                                    where   kHiddenBit = 2^52
                                            kSignificandSize = 52
                                            kExponentBias = 0x3FF + kSignificandSize
                                            kDenormalExponent = -kExponentBias + 1
            boundryMinus    =   createDiyFp ((f mMinus) `shiftL` fromIntegral (e mMinus - e boundryPlus)) (e boundryPlus)
            fstAssert       =   (e boundryPlus) == (e w)
            (ten_mk, mk)    =  getCachedPower (fromIntegral (kMinimalTargetExp - ((fromIntegral (e w)) + kSignificandSize))) (fromIntegral (kMaximalTargetExp - ((fromIntegral (e w)) + kSignificandSize)))
            sndAssert       =   (kMinimalTargetExp <= ((e w) + (e ten_mk) + kSignificandSize)) && (kMaximalTargetExp >= ((e w) + (e ten_mk)  + kSignificandSize))
            scaled_w        = ten_mk * w
            trdAssert       = (e scaled_w) == (e boundryPlus + e ten_mk + kSignificandSize)
            scaledBoundryMinus = boundryMinus * ten_mk
            scaledBoundryPlus   = boundryPlus * ten_mk
            (buffer,kappa)  =   digitGen scaledBoundryMinus scaled_w scaledBoundryPlus
            kSignificandSize=   64
            kMinimalTargetExp  =   (-60)
            kMaximalTargetExp  =   (-32)
            
            
getCachedPower min_exponent max_exponent = (cachedPower, decimalExponent)
    where   kQ  = 64
            kD_1_LOG2_10 = 0.30102999566398114
            k   = ceiling ((min_exponent + kQ  - 1) * kD_1_LOG2_10)
            foo = 348
            index = (((foo + k - 1) `div` kDecimalExponentDistance) + 1) 
            cachedPower  = fst $ powersOfTen !! index
            decimalExponent = snd $ powersOfTen !! index
            kDecimalExponentDistance = 8
            assert = (0 <= index && index < (length powersOfTen)) && (min_exponent <= fromIntegral (e cachedPower)) && (fromIntegral (e cachedPower) <= max_exponent) 

normalize :: DiyFp -> DiyFp
normalize v
            | f v                   == 0 = v
            | f v < (1 `shiftL` 55)      = normalize (createDiyFp ((f v) `shiftL` 8) ((e v) - 8))
            | (f v) .&. (2^63) == 0      = normalize (createDiyFp ((f v) `shiftL` 1) ((e v) - 1))
            | otherwise                  = v

--digitGen :: (DiyFp, DiyFp, DiyFp) -> [Integer]
digitGen low fp high        = (buffer, kappa)
    where   too_low         = createDiyFp ((f low) - unit) (e low)
            too_high        = createDiyFp ((f high) + unit) (e high)
            unit            = 1
            shift           = fromIntegral (-1 * (e fp))
            unsafe_int      = too_high - too_low
            one             = createDiyFp (1 `shiftL` shift) (e fp)
            integrals       = (f too_high) `shiftR` shift
            fractional      = (f too_high) .&. ((f one) -1)
            rest            = (integrals `shiftL` shift) + fractional
            (divisor,divExp)= biggestPowerTen integrals (kSignificandSize - shift)
            length          = 0
            (buffer,kappa)          = findInvariant (divExp + 1) "" length integrals divisor fractional (too_high - too_low) unit shift too_high fp one 
            assert          =(e low == e fp) && (e fp == e high) && (f low + 1 <= f high -1) && ((-60) <= e fp) && (e fp <= (-32))
--            pointless       = calcInvariant kappa "" integrals divisor fractional shift too_high fp unsafe_int one 0 1

findInvariant kappa buffer length integrals divisor fractional unsafe unit shift too_high w one
    |   (kappa > 0) =   if ((integrals `shiftL` shift) + fractional) < f unsafe
                        then  (roundWeed (buffer ++ show (integrals `div` divisor)) (length + 1) (f (too_high - w)) (f unsafe) (((integrals `mod` divisor) `shiftL` shift) + fractional) (divisor `shiftL` shift) unit,kappa -1)
                        else findInvariant (kappa - 1) (buffer ++ show (integrals `div` divisor)) (length + 1) (integrals `mod` divisor) (divisor `div` 10) fractional unsafe unit shift too_high w one
    |   otherwise   =   if (((fractional*10) .&. ((f one) - 1))) < ((f unsafe)*10)
                        then (roundWeed (buffer ++ show ((fractional * 10) `shiftR` shift)) (length + 1) ((f (too_high - w)) * (unit*10)) ((f unsafe)*10) ((fractional*10) .&. ((f one) - 1)) (f one) (unit*10), kappa -1)
                        else findInvariant (kappa - 1) (buffer ++ show ((fractional * 10) `shiftR` shift)) (length + 1) (integrals) (divisor) ((fractional*10) .&. ((f one) - 1)) (createDiyFp (f unsafe *10) (e unsafe)) (unit*10) shift too_high w one
    where hiddenAssert  =   ((e one) >= (-60)) && (fractional < (f one)) && ( (0xFFFFFFFFFFFFFFFF `div` 10) >= f one)


--
--kappaLoop kappa buffer length integrals divisor fractional unsafe unit shift too_high w one
--    | (kappa > 0) && ((((integrals `mod` divisor) `shiftL` shift) + fractional) < f unsafe)  = trace ("RW & buffer: " ++ show buffer) ((kappa -1 + length), roundWeed (buffer ++ show (integrals `div` divisor)) (length + 1) (f (too_high - w)) (f unsafe) (((integrals `mod` divisor) `shiftL` shift) + fractional) (divisor `shiftL` shift) unit)
--    | (kappa > 0) = trace ("buffer: " ++ show buffer) kappaLoop (kappa - 1) (buffer ++ show (integrals `div` divisor)) (length + 1) (integrals `mod` divisor) (divisor `div` 10) fractional unsafe unit shift too_high w one
--    | otherwise =   if ((fractional*10) .&. ((f one) - 1))  < (f unsafe)
--                    then trace ("RW & buffer: " ++ show buffer) ((kappa - 1 + length), roundWeed (buffer ++ show ((fractional * 10) `shiftR` shift)) (length + 1) ((f (too_high - w)) * (unit*10)) ((f unsafe)*10) ((fractional*10) .&. ((f one) - 1)) (f one) (unit*10))
--                    else trace ("buffer: " ++ show buffer) kappaLoop (kappa - 1)  (buffer ++ show ((fractional * 10) `shiftR` shift)) (length + 1) (integrals) (divisor) ((fractional*10) .&. ((f one) - 1)) (createDiyFp (f unsafe *10) (e unsafe)) (unit*10) shift too_high w one
    --hidden assert ((e one) >= (-60)) && (fractional < (f one)) && ( (0xFFFFFFFFFFFFFFFF `div` 10) >= f one)

smallPowerTen = map (10^) [0..9]
--
biggestPowerTen number number_bits = (power,finExp)
    where   assert = (number < (1 `shiftL` (number_bits + 1)))
            exponentPlusOne = (((number_bits + 1) * 1223) `shiftR` 12) + 1
            power = smallPowerTen !! finExp
            finExp =    if (number < (smallPowerTen !! exponentPlusOne))
                        then exponentPlusOne - 1
                        else exponentPlusOne

--calcInvariant kappa buffer integrals divider fractional shift too_high fp unsafe one length unit
--    | (kappa > 0) && (rest < (f unsafe))    = trace ("roundWeed! " ) roundWeed (buffer ++ (show digit)) (length+1) (f (too_high - fp)) (f unsafe) rest (divider `shiftL` shift) unit
--    | (kappa > 0)                           = trace ("kappa " ++ show kappa) calcInvariant (kappa - 1) (buffer ++ (show digit)) (integrals `mod` divider) (divider `div` 10) fractional shift too_high fp unsafe one (length + 1) unit
--    | (((fractional * 5) .&. ((f one `shiftR` 1) - 1)) < (f unsafe * 5)) = trace ("roundWeed 2! ") roundWeed (buffer ++ show ((fractional*5) `shiftR` shift)) (length + 1) ((f (too_high - fp))*unit) (f unsafe * 5) (fractional * 5) (f one `shiftR` 1) (unit*5)
--    | otherwise                             = trace ("otherwise") calcInvariant (kappa - 1) (buffer ++ show ((fractional*5) `shiftR` shift)) integrals divider ((fractional * 5) .&. (f one `shiftR` 1) - 1) shift too_high fp (createDiyFp (f unsafe * 4) (e unsafe + 1)) (createDiyFp (f one `shiftR` 1) (e one + 1)) (length + 1) (unit * 5)
--        where   rest = ((integrals `mod` divider) `shiftL` shift) + fractional
--                digit = integrals `div` divider
--
kSignificandSize = 64

roundWeed buffer length distanceHigh unsafe rest tenkappa unit
    | ((rest < smallDistance) && (unsafe - rest >= tenkappa)) && (((rest + tenkappa) < smallDistance) || (smallDistance - rest >= rest + tenkappa - smallDistance)) =  roundWeed (init buffer ++ [pred (last buffer)]) length distanceHigh unsafe (rest + tenkappa) tenkappa unit
    | otherwise =   if  ((rest < bigDistance) && (unsafe - rest) >= tenkappa) && ((rest + tenkappa < bigDistance) || (bigDistance - rest) > (rest + tenkappa - bigDistance))
                    then Nothing
                    else    if ((2 * unit) <= rest) && (rest <= unsafe - (4 * unit))
                            then Just buffer
                            else Nothing
    where smallDistance = distanceHigh - unit 
          bigDistance = distanceHigh + unit 

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
	((DiyFp 0xfa8fd5a0081c0288 (-1220)), (-348)), 
	((DiyFp 0xbaaee17fa23ebf76 (-1193)), (-340)), 
	((DiyFp 0x8b16fb203055ac76 (-1166)), (-332)), 
	((DiyFp 0xcf42894a5dce35ea (-1140)), (-324)), 
	((DiyFp 0x9a6bb0aa55653b2d (-1113)), (-316)), 
	((DiyFp 0xe61acf033d1a45df (-1087)), (-308)), 
	((DiyFp 0xab70fe17c79ac6ca (-1060)), (-300)), 
	((DiyFp 0xff77b1fcbebcdc4f (-1034)), (-292)), 
	((DiyFp 0xbe5691ef416bd60c (-1007)), (-284)), 
	((DiyFp 0x8dd01fad907ffc3c (-980)), (-276)), 
	((DiyFp 0xd3515c2831559a83 (-954)), (-268)), 
	((DiyFp 0x9d71ac8fada6c9b5 (-927)), (-260)), 
	((DiyFp 0xea9c227723ee8bcb (-901)), (-252)), 
	((DiyFp 0xaecc49914078536d (-874)), (-244)), 
	((DiyFp 0x823c12795db6ce57 (-847)), (-236)), 
	((DiyFp 0xc21094364dfb5637 (-821)), (-228)), 
	((DiyFp 0x9096ea6f3848984f (-794)), (-220)), 
	((DiyFp 0xd77485cb25823ac7 (-768)), (-212)), 
	((DiyFp 0xa086cfcd97bf97f4 (-741)), (-204)), 
	((DiyFp 0xef340a98172aace5 (-715)), (-196)), 
	((DiyFp 0xb23867fb2a35b28e (-688)), (-188)), 
	((DiyFp 0x84c8d4dfd2c63f3b (-661)), (-180)), 
	((DiyFp 0xc5dd44271ad3cdba (-635)), (-172)), 
	((DiyFp 0x936b9fcebb25c996 (-608)), (-164)), 
	((DiyFp 0xdbac6c247d62a584 (-582)), (-156)), 
	((DiyFp 0xa3ab66580d5fdaf6 (-555)), (-148)), 
	((DiyFp 0xf3e2f893dec3f126 (-529)), (-140)), 
	((DiyFp 0xb5b5ada8aaff80b8 (-502)), (-132)), 
	((DiyFp 0x87625f056c7c4a8b (-475)), (-124)), 
	((DiyFp 0xc9bcff6034c13053 (-449)), (-116)), 
	((DiyFp 0x964e858c91ba2655 (-422)), (-108)), 
	((DiyFp 0xdff9772470297ebd (-396)), (-100)), 
	((DiyFp 0xa6dfbd9fb8e5b88f (-369)), (-92)), 
	((DiyFp 0xf8a95fcf88747d94 (-343)), (-84)), 
	((DiyFp 0xb94470938fa89bcf (-316)), (-76)), 
	((DiyFp 0x8a08f0f8bf0f156b (-289)), (-68)), 
	((DiyFp 0xcdb02555653131b6 (-263)), (-60)), 
	((DiyFp 0x993fe2c6d07b7fac (-236)), (-52)), 
	((DiyFp 0xe45c10c42a2b3b06 (-210)), (-44)), 
	((DiyFp 0xaa242499697392d3 (-183)), (-36)), 
	((DiyFp 0xfd87b5f28300ca0e (-157)), (-28)), 
	((DiyFp 0xbce5086492111aeb (-130)), (-20)), 
	((DiyFp 0x8cbccc096f5088cc (-103)), (-12)), 
	((DiyFp 0xd1b71758e219652c (-77)), (-4)), 
	((DiyFp 0x9c40000000000000 (-50)), (4)), 
	((DiyFp 0xe8d4a51000000000 (-24)), (12)), 
	((DiyFp 0xad78ebc5ac620000 (3)), (20)), 
	((DiyFp 0x813f3978f8940984 (30)), (28)), 
	((DiyFp 0xc097ce7bc90715b3 (56)), (36)), 
	((DiyFp 0x8f7e32ce7bea5c70 (83)), (44)), 
	((DiyFp 0xd5d238a4abe98068 (109)), (52)), 
	((DiyFp 0x9f4f2726179a2245 (136)), (60)), 
	((DiyFp 0xed63a231d4c4fb27 (162)), (68)), 
	((DiyFp 0xb0de65388cc8ada8 (189)), (76)), 
	((DiyFp 0x83c7088e1aab65db (216)), (84)), 
	((DiyFp 0xc45d1df942711d9a (242)), (92)), 
	((DiyFp 0x924d692ca61be758 (269)), (100)), 
	((DiyFp 0xda01ee641a708dea (295)), (108)), 
	((DiyFp 0xa26da3999aef774a (322)), (116)), 
	((DiyFp 0xf209787bb47d6b85 (348)), (124)), 
	((DiyFp 0xb454e4a179dd1877 (375)), (132)), 
	((DiyFp 0x865b86925b9bc5c2 (402)), (140)), 
	((DiyFp 0xc83553c5c8965d3d (428)), (148)), 
	((DiyFp 0x952ab45cfa97a0b3 (455)), (156)), 
	((DiyFp 0xde469fbd99a05fe3 (481)), (164)), 
	((DiyFp 0xa59bc234db398c25 (508)), (172)), 
	((DiyFp 0xf6c69a72a3989f5c (534)), (180)), 
	((DiyFp 0xb7dcbf5354e9bece (561)), (188)), 
	((DiyFp 0x88fcf317f22241e2 (588)), (196)), 
	((DiyFp 0xcc20ce9bd35c78a5 (614)), (204)), 
	((DiyFp 0x98165af37b2153df (641)), (212)), 
	((DiyFp 0xe2a0b5dc971f303a (667)), (220)), 
	((DiyFp 0xa8d9d1535ce3b396 (694)), (228)), 
	((DiyFp 0xfb9b7cd9a4a7443c (720)), (236)), 
	((DiyFp 0xbb764c4ca7a44410 (747)), (244)), 
	((DiyFp 0x8bab8eefb6409c1a (774)), (252)), 
	((DiyFp 0xd01fef10a657842c (800)), (260)), 
	((DiyFp 0x9b10a4e5e9913129 (827)), (268)), 
	((DiyFp 0xe7109bfba19c0c9d (853)), (276)), 
	((DiyFp 0xac2820d9623bf429 (880)), (284)), 
	((DiyFp 0x80444b5e7aa7cf85 (907)), (292)), 
	((DiyFp 0xbf21e44003acdd2d (933)), (300)), 
	((DiyFp 0x8e679c2f5e44ff8f (960)), (308)), 
	((DiyFp 0xd433179d9c8cb841 (986)), (316)), 
	((DiyFp 0x9e19db92b4e31ba9 (1013)), (324)), 
	((DiyFp 0xeb96bf6ebadf77d9 (1039)), (332)), 
	((DiyFp 0xaf87023b9bf0ee6b (1066)), (340))]

