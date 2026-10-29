open util/integer

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

fun padd[p1, p2: Pixel]: lone Pixel {
	let x_ = plus[p1.x, p2.x], y_ = plus[p1.y, p2.y] | 
		{ p: Pixel | p.x = x_ and p.y = y_ }  
}

fun psub[p1, p2: Pixel]: lone Pixel {
  let x_ = minus[p1.x, p2.x], y_ = minus[p1.y, p2.y] |
    { p: Pixel | p.x = x_ and p.y = y_ }
}

pred pleq[p1, p2: Pixel] {
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
	{ p: Pixel | pleq[p1, p] and pleq[p, p2] }  
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

fact Unique { one Black and one White }

let PixMap = Pixel -> lone Value
let PixMap1[m] = { some m }


fun NAND[v1, v2: Value] : Value {
  { n: ZRange, b: BitVal | 
  		b = ((v1[n] = SetVal and v2[n] = SetVal) implies ClearVal else SetVal) }
}

pred sameshape[p1, p2: PixMap] {
	
}

// The check Zsize = 1 implies value = {Black, White}
check {lone NAND[Black, White]} for 3 but 1 Grid, 2 Value, 2 BitVal
