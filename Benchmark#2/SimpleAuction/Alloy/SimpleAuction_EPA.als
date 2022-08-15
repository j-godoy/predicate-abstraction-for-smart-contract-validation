// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Address{balance: Int}
one sig Address0x0 extends Address{}
one sig AddressA extends Address{}
one sig AddressB extends Address{}
one sig AddressBeneficiary extends Address{}

//run transicion_S00_a_INV_mediante_met_constructor for 2 EstadoConcreto

// estados concretos
abstract sig EstadoConcreto {
	_auctionStart: Int,
	_biddingTime: Int,
	_beneficiary: Address,
	_highestBidder: Address,
	_highestBid: Int,
	_pendingReturns: Address -> lone Int,
	_ended: Bool,
	_now: Int //lo agrego para simular el paso del tiempo
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}

pred invarianteSinBeneficiary[e:EstadoConcreto] {
	//Una Address no puede tener balance negativo
	(no a:Address | a.balance < 0)
	
	(Address0x0 in e._pendingReturns.Int and e._pendingReturns[Address0x0] = 0)
	(all a:Address | a in e._pendingReturns.Int implies e._pendingReturns[a] >= 0)

	e._highestBid >= 0
//	highestBidEslaApuestaMayor[e] or #(e._pendingReturns.Int) = 1 //or e._ended = True

	e._auctionStart >= 0
	e._biddingTime >= 0

	e._highestBidder = Address0x0 implies #(e._pendingReturns.Int) = 1

	e._ended = True implies e._now >= e._auctionStart.add[e._biddingTime]
}

pred invariante[e:EstadoConcreto] {
	invarianteSinBeneficiary[e]
	e._beneficiary = AddressBeneficiary
}

/*pred highestBidEslaApuestaMayor[e:EstadoConcreto] {
	(some a1:Address | a1 = e._highestBidder and a1 !in e._pendingReturns.Int and
			(all a2:Address | a2 in e._pendingReturns.Int implies
				e._highestBid >= e._pendingReturns[a2]
			)
	) or
	(some a1:Address | a1 = e._highestBidder and e._highestBid>0 and a1 in e._pendingReturns.Int and
		(all a2:Address | a2 in e._pendingReturns.Int implies
				e._pendingReturns[a1] >= e._pendingReturns[a2]
		)
	)
}*/

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, value: Int, biddingTime: Int ] {
	//Pre
	ein._beneficiary = Address0x0
	ein._highestBidder = Address0x0
	ein._highestBid = 0
	ein._pendingReturns = Address0x0 -> 0
	ein._ended = False

	//Post
	eout._auctionStart = 1
	eout._beneficiary = AddressBeneficiary
	eout._biddingTime = biddingTime

	//eout._auctionStart = ein._auctionStart
	//eout._biddingTime = ein._biddingTime
	//eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	//eout._now = ein._now.add[1]
	eout._now = ein._now
}

pred pre_bid[ein:EstadoConcreto] {
	ein._now <= ein._auctionStart.add[ein._biddingTime]
	//(ein._beneficiary != Address0x0)
}

pred met_bid[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int] {
	//PRE
	pre_bid[ein]
	(ein._beneficiary != Address0x0)
	sender != Address0x0
	value > ein._highestBid

	//POST
	ein._highestBidder != Address0x0 =>
		(eout._pendingReturns = ein._pendingReturns++ein._highestBidder->ein._pendingReturns[ein._highestBidder].add[ein._highestBid])
	else
		(eout._pendingReturns = ein._pendingReturns)
	
	eout._highestBidder = sender
	eout._highestBid = value

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	//eout._highestBidder = ein._highestBidder
	//eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now
}

pred pre_withdraw[ein: EstadoConcreto] {
	//highestBidEslaApuestaMayor[ein]
	some a:Address | a in ein._pendingReturns.Int
				and ein._pendingReturns[a] > 0
	//(ein._beneficiary != Address0x0)
}

pred met_withdraw[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	ein._pendingReturns[sender] > 0
	(ein._beneficiary != Address0x0)
	sender != Address0x0
	sender in ein._pendingReturns.Int

	//POST

	//(let pr = pendingReturns[sender] |
	eout._pendingReturns = ein._pendingReturns++sender -> 0

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	//eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now
}

pred pre_auctionEnd[ein: EstadoConcreto] {
	(ein._now >= (ein._auctionStart.add[ein._biddingTime])) // auction did not yet end
	(ein._ended = False)
	(ein._beneficiary != Address0x0)
}

pred met_auctionEnd[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//PRE
	pre_auctionEnd[ein]
	sender != Address0x0

	//POST
	eout._ended = True
	//eout._beneficiary.balance = ein._beneficiary.balance.add[ein._highestBid]

	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	//eout._ended = ein._ended
	eout._now = ein._now
}

pred pre_t[e:EstadoConcreto] {
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int, timeElapsed: Int] {
	//PRE
	timeElapsed >= 0
	
	eout._auctionStart = ein._auctionStart
	eout._biddingTime = ein._biddingTime
	eout._beneficiary = ein._beneficiary
	eout._highestBidder = ein._highestBidder
	eout._highestBid = ein._highestBid
	eout._pendingReturns = ein._pendingReturns
	eout._ended = ein._ended
	eout._now = ein._now.add[1]
}

//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////
pred partitionS00[e: EstadoConcreto]{ // 
	(invarianteSinBeneficiary[e])
	(e._beneficiary = Address0x0)
}

pred partitionINV[e: EstadoConcreto]{
	not invariante[e]
}





pred partitionS01[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS02[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS03[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS04[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS05[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS06[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS07[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS08[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS09[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS10[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS11[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and pre_t[e]
}

pred partitionS12[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and pre_t[e]
}

pred partitionS13[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS14[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS15[e: EstadoConcreto]{
	(invariante[e])
	pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}

pred partitionS16[e: EstadoConcreto]{
	(invariante[e])
	not pre_bid[e] and not pre_withdraw[e] and not pre_auctionEnd[e] and not pre_t[e]
}

pred transicion_S00_a_S01_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S02_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S03_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S04_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S05_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S06_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S07_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S08_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S09_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S10_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S11_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S12_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S13_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S14_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S15_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S00_a_S16_mediante_met_constructor{
	(partitionS00[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_constructor [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S00_a_S01_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S02_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S03_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S04_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S05_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S06_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S07_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S08_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S09_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S10_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S11_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S12_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S13_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S14_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S15_mediante_met_constructor for 2 EstadoConcreto
run transicion_S00_a_S16_mediante_met_constructor for 2 EstadoConcreto
pred transicion_S01_a_S01_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S06_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S07_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S08_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S09_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S10_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S11_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S12_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S13_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S14_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S15_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S16_mediante_met_bid{
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S06_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S07_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S08_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S09_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S10_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S11_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S12_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S13_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S14_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S15_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S16_mediante_met_bid{
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S06_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S07_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S08_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S09_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S10_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S11_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S12_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S13_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S14_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S15_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S16_mediante_met_bid{
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S06_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S07_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S08_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S09_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S10_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S11_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S12_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S13_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S14_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S15_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S16_mediante_met_bid{
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S06_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S07_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S08_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S09_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S10_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S11_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S12_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S13_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S14_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S15_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S16_mediante_met_bid{
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S01_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S02_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S03_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S04_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S05_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S06_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S07_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S08_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S09_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S10_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S11_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S12_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S13_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S14_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S15_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S16_mediante_met_bid{
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S01_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S02_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S03_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S04_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S05_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S06_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S07_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S08_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S09_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S10_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S11_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S12_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S13_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S14_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S15_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S16_mediante_met_bid{
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S01_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S02_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S03_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S04_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S05_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S06_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S07_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S08_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S09_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S10_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S11_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S12_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S13_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S14_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S15_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S08_a_S16_mediante_met_bid{
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S01_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S02_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S03_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S04_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S05_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S06_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S07_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S08_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S09_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S10_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S11_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S12_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S13_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S14_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S15_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S09_a_S16_mediante_met_bid{
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S01_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S02_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S03_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S04_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S05_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S06_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S07_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S08_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S09_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S10_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S11_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S12_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S13_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S14_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S15_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S10_a_S16_mediante_met_bid{
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S01_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S02_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S03_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S04_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S05_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S06_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S07_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S08_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S09_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S10_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S11_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S12_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S13_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S14_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S15_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S11_a_S16_mediante_met_bid{
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S01_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S02_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S03_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S04_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S05_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S06_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S07_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S08_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S09_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S10_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S11_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S12_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S13_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S14_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S15_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S12_a_S16_mediante_met_bid{
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S01_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S02_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S03_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S04_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S05_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S06_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S07_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S08_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S09_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S10_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S11_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S12_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S13_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S14_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S15_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S13_a_S16_mediante_met_bid{
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S01_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S02_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S03_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S04_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S05_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S06_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S07_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S08_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S09_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S10_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S11_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S12_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S13_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S14_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S15_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S14_a_S16_mediante_met_bid{
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S01_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S02_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S03_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S04_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S05_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S06_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S07_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S08_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S09_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S10_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S11_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S12_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S13_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S14_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S15_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S15_a_S16_mediante_met_bid{
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S01_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S02_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S03_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S04_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S05_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S06_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S07_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S08_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S09_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S10_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S11_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S12_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S13_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S14_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S15_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S16_a_S16_mediante_met_bid{
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_bid [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S01_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_bid for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_bid for 2 EstadoConcreto
pred transicion_S01_a_S01_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S11_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S12_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S13_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S14_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S15_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S16_mediante_met_withdraw{
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S11_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S12_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S13_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S14_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S15_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S16_mediante_met_withdraw{
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S11_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S12_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S13_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S14_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S15_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S16_mediante_met_withdraw{
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S11_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S12_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S13_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S14_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S15_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S16_mediante_met_withdraw{
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S11_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S12_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S13_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S14_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S15_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S16_mediante_met_withdraw{
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S11_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S12_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S13_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S14_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S15_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S16_mediante_met_withdraw{
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S11_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S12_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S13_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S14_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S15_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S16_mediante_met_withdraw{
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S11_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S12_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S13_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S14_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S15_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S16_mediante_met_withdraw{
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S11_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S12_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S13_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S14_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S15_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S16_mediante_met_withdraw{
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S11_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S12_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S13_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S14_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S15_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S16_mediante_met_withdraw{
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S01_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S02_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S03_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S04_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S05_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S06_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S07_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S08_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S09_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S10_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S11_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S12_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S13_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S14_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S15_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S16_mediante_met_withdraw{
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S01_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S02_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S03_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S04_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S05_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S06_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S07_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S08_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S09_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S10_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S11_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S12_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S13_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S14_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S15_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S16_mediante_met_withdraw{
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S01_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S02_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S03_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S04_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S05_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S06_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S07_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S08_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S09_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S10_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S11_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S12_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S13_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S14_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S15_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S16_mediante_met_withdraw{
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S01_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S02_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S03_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S04_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S05_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S06_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S07_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S08_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S09_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S10_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S11_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S12_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S13_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S14_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S15_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S16_mediante_met_withdraw{
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S01_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S02_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S03_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S04_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S05_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S06_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S07_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S08_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S09_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S10_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S11_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S12_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S13_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S14_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S15_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S16_mediante_met_withdraw{
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S01_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S02_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S03_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S04_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S05_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S06_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S07_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S08_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S09_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S10_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S11_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S12_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S13_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S14_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S15_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S16_mediante_met_withdraw{
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_withdraw [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S01_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_withdraw for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_withdraw for 2 EstadoConcreto
pred transicion_S01_a_S01_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S02_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S03_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S04_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S05_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S06_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S07_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S08_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S09_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S10_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S11_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S12_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S13_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S14_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S15_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S01_a_S16_mediante_met_auctionEnd{
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S01_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S02_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S03_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S04_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S05_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S06_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S07_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S08_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S09_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S10_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S11_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S12_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S13_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S14_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S15_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S02_a_S16_mediante_met_auctionEnd{
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S01_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S02_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S03_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S04_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S05_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S06_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S07_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S08_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S09_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S10_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S11_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S12_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S13_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S14_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S15_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S03_a_S16_mediante_met_auctionEnd{
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S01_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S02_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S03_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S04_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S05_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S06_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S07_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S08_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S09_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S10_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S11_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S12_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S13_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S14_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S15_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S04_a_S16_mediante_met_auctionEnd{
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S01_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S02_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S03_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S04_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S05_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S06_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S07_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S08_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S09_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S10_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S11_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S12_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S13_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S14_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S15_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S05_a_S16_mediante_met_auctionEnd{
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S01_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S02_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S03_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S04_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S05_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S06_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S07_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S08_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S09_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S10_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S11_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S12_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S13_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S14_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S15_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S06_a_S16_mediante_met_auctionEnd{
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S01_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S02_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S03_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S04_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S05_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S06_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S07_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S08_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S09_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S10_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S11_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S12_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S13_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S14_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S15_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S07_a_S16_mediante_met_auctionEnd{
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S01_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S02_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S03_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S04_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S05_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S06_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S07_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S08_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S09_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S10_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S11_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S12_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S13_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S14_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S15_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S08_a_S16_mediante_met_auctionEnd{
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S01_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S02_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S03_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S04_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S05_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S06_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S07_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S08_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S09_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S10_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S11_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S12_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S13_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S14_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S15_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S09_a_S16_mediante_met_auctionEnd{
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S01_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S02_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S03_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S04_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S05_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S06_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S07_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S08_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S09_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S10_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S11_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S12_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S13_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S14_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S15_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S10_a_S16_mediante_met_auctionEnd{
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S01_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S02_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S03_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S04_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S05_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S06_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S07_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S08_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S09_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S10_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S11_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S12_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S13_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S14_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S15_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S11_a_S16_mediante_met_auctionEnd{
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S01_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S02_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S03_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S04_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S05_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S06_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S07_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S08_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S09_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S10_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S11_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S12_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S13_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S14_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S15_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S12_a_S16_mediante_met_auctionEnd{
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S01_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S02_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S03_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S04_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S05_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S06_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S07_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S08_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S09_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S10_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S11_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S12_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S13_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S14_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S15_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S13_a_S16_mediante_met_auctionEnd{
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S01_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S02_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S03_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S04_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S05_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S06_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S07_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S08_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S09_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S10_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S11_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S12_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S13_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S14_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S15_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S14_a_S16_mediante_met_auctionEnd{
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S01_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S02_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S03_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S04_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S05_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S06_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S07_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S08_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S09_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S10_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S11_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S12_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S13_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S14_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S15_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S15_a_S16_mediante_met_auctionEnd{
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S01_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S02_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S03_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S04_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S05_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S06_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S07_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S08_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S09_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S10_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S11_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S12_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S13_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S14_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S15_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

pred transicion_S16_a_S16_mediante_met_auctionEnd{
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address | v10 != Address0x0 and met_auctionEnd [EstadoConcretoInicial, EstadoConcretoFinal, v10])
}

run transicion_S01_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_auctionEnd for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_auctionEnd for 2 EstadoConcreto
pred transicion_S01_a_S01_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S08_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S09_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S10_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S11_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S12_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S13_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S14_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S15_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S16_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S08_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S09_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S10_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S11_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S12_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S13_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S14_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S15_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S16_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S08_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S09_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S10_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S11_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S12_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S13_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S14_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S15_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S16_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S08_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S09_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S10_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S11_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S12_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S13_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S14_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S15_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S16_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S08_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S09_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S10_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S11_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S12_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S13_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S14_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S15_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S16_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S08_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S09_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S10_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S11_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S12_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S13_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S14_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S15_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S16_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S08_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S09_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S10_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S11_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S12_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S13_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S14_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S15_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S16_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S01_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S02_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S03_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S04_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S05_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S06_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S07_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S08_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S09_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S10_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S11_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S12_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S13_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S14_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S15_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S08_a_S16_mediante_met_t{
	(partitionS08[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S01_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S02_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S03_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S04_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S05_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S06_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S07_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S08_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S09_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S10_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S11_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S12_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S13_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S14_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S15_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S09_a_S16_mediante_met_t{
	(partitionS09[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S01_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S02_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S03_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S04_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S05_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S06_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S07_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S08_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S09_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S10_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S11_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S12_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S13_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S14_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S15_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S10_a_S16_mediante_met_t{
	(partitionS10[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S01_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S02_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S03_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S04_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S05_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S06_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S07_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S08_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S09_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S10_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S11_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S12_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S13_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S14_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S15_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S11_a_S16_mediante_met_t{
	(partitionS11[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S01_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S02_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S03_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S04_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S05_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S06_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S07_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S08_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S09_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S10_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S11_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S12_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S13_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S14_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S15_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S12_a_S16_mediante_met_t{
	(partitionS12[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S01_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S02_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S03_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S04_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S05_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S06_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S07_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S08_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S09_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S10_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S11_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S12_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S13_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S14_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S15_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S13_a_S16_mediante_met_t{
	(partitionS13[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S01_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S02_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S03_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S04_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S05_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S06_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S07_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S08_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S09_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S10_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S11_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S12_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S13_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S14_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S15_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S14_a_S16_mediante_met_t{
	(partitionS14[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S01_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S02_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S03_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S04_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S05_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S06_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S07_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S08_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S09_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S10_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S11_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S12_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S13_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S14_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S15_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S15_a_S16_mediante_met_t{
	(partitionS15[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S01_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S02_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S03_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S04_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S05_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S06_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S07_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S08_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS08[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S09_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS09[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S10_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS10[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S11_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS11[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S12_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS12[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S13_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS13[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S14_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS14[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S15_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS15[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S16_a_S16_mediante_met_t{
	(partitionS16[EstadoConcretoInicial])
	(partitionS16[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S01_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S02_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S03_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S04_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S05_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S06_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S07_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S08_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S09_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S10_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S11_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S12_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S13_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S14_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S15_a_S16_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S01_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S02_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S03_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S04_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S05_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S06_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S07_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S08_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S09_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S10_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S11_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S12_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S13_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S14_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S15_mediante_met_t for 2 EstadoConcreto
run transicion_S16_a_S16_mediante_met_t for 2 EstadoConcreto
