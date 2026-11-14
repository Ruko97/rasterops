open util/integer
open util/ternary

one sig Grid {
	xsize: Int,
	ysize: Int, 
	zsize: Int
} {
	xsize > 0
	ysize > 0
	zsize > 0
}

let XRange = { x: Int | x >= 0 and x < Grid.xsize }
let YRange = { y: Int | y >= 0 and y < Grid.ysize }
let ZRange = { z: Int | z >= 0 and z < Grid.zsize }

sig Pixel {
	x: Int,
	y: Int
} {
	x in XRange
	y in YRange
}

sig PixelPair {
	pix1: Pixel,
	pix2: Pixel
}

fun p_add[p1, p2: Pixel]: lone Pixel {
	let x_ = plus[p1.x, p2.x], y_ = plus[p1.y, p2.y] | 
		{ p: Pixel | p.x = x_ and p.y = y_ }  
}

fun p_sub[p1, p2: Pixel]: lone Pixel {
  let x_ = minus[p1.x, p2.x], y_ = minus[p1.y, p2.y] |
    { p: Pixel | p.x = x_ and p.y = y_ }
}

pred p_leq[p1, p2: Pixel] {
	p1.x <= p2.x and p1.y <= p2.y
}

fun offset[p1, p2: Pixel]: one Pixel {
	// Since there is chance of overflow in the plus operation, 
	// i am using if here
	let x_ = (p2.x < minus[Grid.xsize, p1.x]) 
				implies plus[p1.x, p2.x]
				else minus[p2.x, minus[Grid.xsize, p1.x]],
		 y_ = (p2.y < minus[Grid.ysize, p1.y])
				implies plus[p1.y, p2.y]
				else minus[p2.y, minus[Grid.ysize, p1.y]] | 
	{ p: Pixel | p.x = x_ and p.y = y_ }
}

fun rect[p1, p2: Pixel]: set Pixel {
	{ p: Pixel | p_leq[p1, p] and p_leq[p, p2] }  
}

fun pmax[p1, p2: Pixel]: one Pixel {
	{ p: Pixel | p.x = larger[p1.x, p2.x] 
			and p.y = larger[p1.y, p2.y] }
}

fun pmin[p1, p2: Pixel]: one Pixel {
	{ p: Pixel | p.x = smaller[p1.x, p2.x] 
			and p.y = smaller[p1.y, p2.y] }
}

abstract sig BitVal { bit: Int }
one sig ClearVal extends BitVal {} { bit = 0 }
one sig SetVal extends BitVal {} { bit = 1 } 

let Value = ZRange -> one BitVal

let Black = ZRange -> ClearVal
let White = ZRange -> SetVal

assert ZsizeOneImpliesBlackOrWhite {
	all v: Value |
		Grid.zsize = 1 implies (v = Black or v = White)
}
check ZsizeOneImpliesBlackOrWhite for 4 but exactly 1 Grid

let PixMap = Pixel -> ZRange -> lone BitVal

assert AtMostOneBitVal {
	all t: TestMaps, p: Pixel, z: ZRange | lone t.maps[p][z]
}
check AtMostOneBitVal for 4

pred PixMap1[m: PixMap] { some m }

pred rectangle[m: PixMap] {
	PixMap1[m]
	some p1, p2: Pixel | 
		dom[m] = rect[p1, p2]
}

pred overlaps[m1, m2: PixMap] {
	some (dom[m1] & dom[m2])
}


fun v_NAND[v1, v2: Value] : Value {
  { n: ZRange, b: BitVal | 
  		b = ((v1[n] = SetVal and v2[n] = SetVal) implies ClearVal else SetVal) }
}

-- Helper function. Returns a Pixel -> Pixel relation that shifts every pixel by the offset p0.
fun shift[p0: Pixel]: Pixel -> Pixel {
	{ p, q: Pixel | q = offset[p0, p] }
}

-- We need to use one here cause some does not work with the shift function.
-- We need to ensure that there is exactly one offset for each pixel in the PixMap.
pred sameshape[m1, m2: PixMap] {
	one p0: Pixel | 
		(dom[m1]).(shift[p0]) = dom[m2]
}

pred mappair[m1, m2: PixMap] {
	sameshape[m1, m2]
}

-- We need to use one here cause some does not work with the shift function.
-- We need to ensure that there is exactly one offset for each pixel in the PixMap.
pred samepos[p1: Pixel, m1: PixMap, p2: Pixel, m2: PixMap] {
	mappair[m1, m2]
	p1 in dom[m1] and p2 in dom[m2]
	one p0: Pixel | 
		(dom[m1]).(shift[p0]) = dom[m2] and
		p1 -> p2 in shift[p0]
}

fun m_nand[m1, m2: PixMap]: PixMap {
	let m = { p2: Pixel, n: ZRange, b: BitVal | 
		mappair[m1, m2] and
		p2 in dom[m2] and
		one p1: dom[m1] | 
			samepos[p1, m1, p2, m2] and
			(n -> b) in v_NAND[m1[p1], m2[p2]] 
	} | m	
}

fun m_noop[m: PixMap]: PixMap {
	m
}

fun m_not[m: PixMap]: PixMap {
	m_nand[m, m]
}

fun m_set[m: PixMap]: PixMap {
	m_nand[m, m_not[m]]
}

fun m_clear[m: PixMap]: PixMap {
	m_not[m_set[m]]
}

fun m_and[m1, m2: PixMap]: PixMap {
	m_not[m_nand[m1, m2]]
}

fun m_or[m1, m2: PixMap]: PixMap {
	m_nand[m_not[m1], m_not[m2]]
}

fun m_xor[m1, m2: PixMap]: PixMap {
	m_and[m_or[m1, m2], m_nand[m1, m2]]
}

fun m_nor[m1, m2: PixMap]: PixMap {
	m_not[m_or[m1, m2]]
}

fun m_copy[m1, m2: PixMap]: PixMap {
	m_or[m1, m_clear[m2]]
}

fun m_copyInverted[m1, m2: PixMap]: PixMap {
	m_or[m_not[m1], m_clear[m2]]
}

fun m_andReverse[m1, m2: PixMap]: PixMap {
	m_and[m1, m_not[m2]]
}

fun m_andInverted[m1, m2: PixMap]: PixMap {
	m_and[m_not[m1], m2]
}

fun m_orReverse[m1, m2: PixMap]: PixMap {
	m_or[m1, m_not[m2]]
}

fun m_orInverted[m1, m2: PixMap]: PixMap {
	m_or[m_not[m1], m2]
}

fun m_equiv[m1, m2: PixMap]: PixMap {
	m_xor[m_not[m1], m2]
}

fact CompleteGrid { all i: XRange, j: YRange | one p: Pixel | p.x = i and p.y = j }

-- NOTE: Field types are written inline instead of using the PixMap macro,
-- because Alloy drops the `lone` multiplicity when a field is declared via a let macro.
sig TestMaps {
	maps: Pixel -> ZRange -> lone BitVal
} {
	some maps
	PixMap1[maps]
}

assert SameposImpliesSameshape {
  all m1, m2: PixMap, p1, p2: Pixel | 
	samepos[p1, m1, p2, m2] implies sameshape[m1, m2]
}

check SameposImpliesSameshape for 4 but exactly 1 Grid, 5 TestMaps

pred showTwoSetups {
	some disj t1, t2: TestMaps {
		some p1, p2: Pixel | 
			samepos[p1, t1.maps, p2, t1.maps] and 
			samepos[p1, t2.maps, p2, t2.maps] and
			t1.maps != t2.maps
	}
}

run showTwoSetups for 4 but exactly 1 Grid, 6 Pixel, 2 TestMaps

assert MapPairImpliesNANDCommutative {
	all t1, t2: TestMaps |
		let m1 = t1.maps, m2 = t2.maps |
			mappair[m1, m2] and dom[m1] = dom[m2] implies m_nand[m1, m2] = m_nand[m2, m1]
}

check MapPairImpliesNANDCommutative for 4 but exactly 1 Grid, 4 Pixel, 2 TestMaps


sig Display {
	screen: Pixel -> ZRange -> lone BitVal
}

pred deltaDisplay{
	dom[Display.screen'] = dom[Display.screen]
}

enum Op1 { NOOP, NOT, CLEAR, SET }
enum Op2 { 
	AND, OR, XOR, NAND, NOR, COPY, COPYINVERTED, ANDREVERSE, 
	ANDINVERTED, ORREVERSE, ORINVERTED, EQUIV 
}

fun applyOp1[op: Op1, m: PixMap]: PixMap {
	op = NOOP implies m_noop[m] else
	op = NOT implies m_not[m] else
	op = CLEAR implies m_clear[m] else
	m_set[m]
}

fun applyOp2[op: Op2, m1, m2: PixMap]: PixMap {
	op = AND implies m_and[m1, m2] else
	op = OR implies m_or[m1, m2] else
	op = XOR implies m_xor[m1, m2] else
	op = NAND implies m_nand[m1, m2] else
	op = NOR implies m_nor[m1, m2] else
	op = COPY implies m_copy[m1, m2] else
	op = COPYINVERTED implies m_copyInverted[m1, m2] else
	op = ANDREVERSE implies m_andReverse[m1, m2] else
	op = ANDINVERTED implies m_andInverted[m1, m2] else
	op = ORREVERSE implies m_orReverse[m1, m2] else
	op = ORINVERTED implies m_orInverted[m1, m2] else
	m_equiv[m1, m2]
}

fun rasterOp1[screen: PixMap, area: set Pixel, op: Op1]: PixMap {
	screen ++ applyOp1[op, area <: screen]
}

fun rasterOp2[screen: PixMap, area: set Pixel, from: Pixel, op: Op2]: PixMap {
	let src = (area.(shift[from])) <: screen, 
		dst = area <: screen |
			screen ++ applyOp2[op, src, dst]
}


pred validPixmap[m: PixMap] {
	all p: dom[m], z: ZRange | one m[p][z]
}

sig SepPair {
	map1: Pixel -> ZRange -> lone BitVal,
	map2: Pixel -> ZRange -> lone BitVal,
} {
	validPixmap[map1]
	validPixmap[map2]
	seppair[map1, map2]
}

pred seppair[m1, m2: PixMap] {
	mappair[m1, m2]
	not overlaps[m1, m2]
}

-- Copyswap is a function that returns a map between the before and after states of a SepPair. 
fun copyswap: SepPair -> SepPair {
	{ s, s_a: SepPair | 
		seppair[s.map1, s.map2] and
		s_a.map1 = m_copy[s.map2, s.map1] and
		s_a.map2 = m_copy[s.map1, s.map2]
	}
}

fun xor1: SepPair -> SepPair {
	{ s, s_a: SepPair | 
		seppair[s.map1, s.map2] and
		s_a.map1 = m_xor[s.map2, s.map1] and
		s_a.map2 = s.map2
	}
}

fun xor2: SepPair -> SepPair {
	{ s, s_a: SepPair | 
		seppair[s.map1, s.map2] and
		s_a.map1 = s.map1 and
		s_a.map2 = m_xor[s.map1, s.map2]
	}
}

pred swap121[s, s_a: SepPair] {
	some m1, m2: SepPair | s -> m1 in xor1 and m1 -> m2 in xor2 and m2 -> s_a in xor1
}

pred swap212[s, s_a: SepPair] {
	some m1, m2: SepPair | s -> m1 in xor2 and m1 -> m2 in xor1 and m2 -> s_a in xor2
}

assert seppairImpliesXorSwapIff {
    all s, s121, s212: SepPair |
        (swap121[s, s121] and swap212[s, s212])
        implies (s121.map1 = s212.map1 and s121.map2 = s212.map2)
}

check seppairImpliesXorSwapIff for 4 but exactly 1 Grid, 4 Pixel, 2 TestMaps

assert xorSwapIsCopySwap {
	all s, s_a: SepPair |
		swap121[s, s_a] implies s -> s_a in copyswap
}

check xorSwapIsCopySwap for 4 but exactly 1 Grid, 4 Pixel, 2 TestMaps
