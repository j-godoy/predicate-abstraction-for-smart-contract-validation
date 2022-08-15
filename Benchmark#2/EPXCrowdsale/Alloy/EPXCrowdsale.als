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
one sig AddressBene0x7A29e extends Address{}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}

sig Deposit{d: Address->lone Int}

// estados concretos
abstract sig EstadoConcreto {
	_owner: Address,
	_admin: Address,
	_tokensRemaining: Int,
	_beneficiaryWallet: Address,
	_amountRaisedInWei: Int,
	_fundingMinCapInWei: Int,
	_currentStatus: lone State,
	_fundingStartBlock: Int,
	_fundingEndBlock: Int,
	_isCrowdSaleClosed: Bool,
	_areFundsReleasedToBeneficiary: Bool,
	_isCrowdSaleSetup: Bool,
	_usersEPXfundValue: Deposit,
	_balance: Int,
	_blockNumber: Int, //lo agrego para simular el paso del tiempo
}

abstract sig State{}
one sig CrowdsaleDeployedToChain extends State {}
one sig CrowdsaleIsSetup extends State{}
one sig InProgress_Eth_low_Softcap extends State{}
one sig InProgress_Eth_ge_Softcap extends State{}
one sig Unsuccessful_Eth_low_Softcap extends State{}
one sig Successful_EPX_ge_Hardcap extends State{}
one sig Successful_Eth_ge_Softcap extends State{}


fun LIMIT[]: Int {5}


//run transicion_S01_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq

pred invariante [e:EstadoConcreto] {
	e._admin != Address0x0
	e._owner != Address0x0
	e._admin = e._owner
	
	no e._currentStatus iff e._admin = Address0x0
	
	/*
	e._currentStatus = InProgress_Eth_low_Softcap implies
		((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber <= e._fundingEndBlock and e._blockNumber >= e._fundingStartBlock))
		
	e._currentStatus = Unsuccessful_Eth_low_Softcap implies 
	((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock))
	
	e._currentStatus = Successful_EPX_ge_Hardcap implies
		((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._tokensRemaining = 0))
		
	e._currentStatus = Successful_Eth_ge_Softcap implies 
		((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock) and (e._tokensRemaining > 0))
		
	e._currentStatus = InProgress_Eth_ge_Softcap implies
		((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._tokensRemaining > 0) and (e._blockNumber <= e._fundingEndBlock))
		*/

	e._isCrowdSaleSetup = False implies e._currentStatus = CrowdsaleDeployedToChain
	e._isCrowdSaleClosed = True implies e._currentStatus != CrowdsaleDeployedToChain
	e._isCrowdSaleClosed = True implies
		(((e._amountRaisedInWei < e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock)) or 
		(e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._tokensRemaining = 0) or
		((e._amountRaisedInWei >= e._fundingMinCapInWei) and (e._blockNumber > e._fundingEndBlock) and (e._tokensRemaining > 0)))
	
	((e._tokensRemaining > 0 or e._fundingStartBlock > 0 or e._fundingEndBlock > 0 or e._fundingMinCapInWei > 0)
		implies e._currentStatus != CrowdsaleDeployedToChain)
	e._areFundsReleasedToBeneficiary = True implies e._isCrowdSaleSetup = True

	//No Negativos
	e._blockNumber >=0 and e._fundingEndBlock >=0 and e._fundingStartBlock >= 0
	e._balance >= 0 and e._blockNumber >= 0 and e._amountRaisedInWei >=0
	/*e._tokensRemaining >= 0*/
	 e._fundingMinCapInWei >=0
	//sumatoria[e._usersEPXfundValue, e._amountRaisedInWei]

	//fixed size: Int= 0,1,2,3; max length=4
	all d0:Address | e._usersEPXfundValue.d[d0] >= 0 and e._usersEPXfundValue.d[d0] <= LIMIT[]
	#(e._usersEPXfundValue.d.Int) <= 4
}

fun sumof[s:seq Int]: Int {
	s=none->none implies 0
	else s=0->0 implies 0
	else s=0->1 implies 1
	else s=0->2 implies 2
	else s=0->3 implies 3
	else s=0->4 implies 4
	else s=0->5 implies 5
	else s=0->0+1->0 implies 0
	else s=0->0+1->1 implies 1
	else s=0->0+1->2 implies 2
	else s=0->0+1->3 implies 3
	else s=0->0+1->4 implies 4
	else s=0->0+1->5 implies 5
	else s=0->1+1->0 implies 1
	else s=0->1+1->1 implies 2
	else s=0->1+1->2 implies 3
	else s=0->1+1->3 implies 4
	else s=0->1+1->4 implies 5
	else s=0->1+1->5 implies 6
	else s=0->2+1->0 implies 2
	else s=0->2+1->1 implies 3
	else s=0->2+1->2 implies 4
	else s=0->2+1->3 implies 5
	else s=0->2+1->4 implies 6
	else s=0->2+1->5 implies 7
	else s=0->3+1->0 implies 3
	else s=0->3+1->1 implies 4
	else s=0->3+1->2 implies 5
	else s=0->3+1->3 implies 6
	else s=0->3+1->4 implies 7
	else s=0->3+1->5 implies 8
	else s=0->4+1->0 implies 4
	else s=0->4+1->1 implies 5
	else s=0->4+1->2 implies 6
	else s=0->4+1->3 implies 7
	else s=0->4+1->4 implies 8
	else s=0->4+1->5 implies 9
	else s=0->5+1->0 implies 5
	else s=0->5+1->1 implies 6
	else s=0->5+1->2 implies 7
	else s=0->5+1->3 implies 8
	else s=0->5+1->4 implies 9
	else s=0->5+1->5 implies 10
	else s=0->0+1->0+2->0 implies 0
	else s=0->0+1->0+2->1 implies 1
	else s=0->0+1->0+2->2 implies 2
	else s=0->0+1->0+2->3 implies 3
	else s=0->0+1->0+2->4 implies 4
	else s=0->0+1->0+2->5 implies 5
	else s=0->0+1->1+2->0 implies 1
	else s=0->0+1->1+2->1 implies 2
	else s=0->0+1->1+2->2 implies 3
	else s=0->0+1->1+2->3 implies 4
	else s=0->0+1->1+2->4 implies 5
	else s=0->0+1->1+2->5 implies 6
	else s=0->0+1->2+2->0 implies 2
	else s=0->0+1->2+2->1 implies 3
	else s=0->0+1->2+2->2 implies 4
	else s=0->0+1->2+2->3 implies 5
	else s=0->0+1->2+2->4 implies 6
	else s=0->0+1->2+2->5 implies 7
	else s=0->0+1->3+2->0 implies 3
	else s=0->0+1->3+2->1 implies 4
	else s=0->0+1->3+2->2 implies 5
	else s=0->0+1->3+2->3 implies 6
	else s=0->0+1->3+2->4 implies 7
	else s=0->0+1->3+2->5 implies 8
	else s=0->0+1->4+2->0 implies 4
	else s=0->0+1->4+2->1 implies 5
	else s=0->0+1->4+2->2 implies 6
	else s=0->0+1->4+2->3 implies 7
	else s=0->0+1->4+2->4 implies 8
	else s=0->0+1->4+2->5 implies 9
	else s=0->0+1->5+2->0 implies 5
	else s=0->0+1->5+2->1 implies 6
	else s=0->0+1->5+2->2 implies 7
	else s=0->0+1->5+2->3 implies 8
	else s=0->0+1->5+2->4 implies 9
	else s=0->0+1->5+2->5 implies 10
	else s=0->1+1->0+2->0 implies 1
	else s=0->1+1->0+2->1 implies 2
	else s=0->1+1->0+2->2 implies 3
	else s=0->1+1->0+2->3 implies 4
	else s=0->1+1->0+2->4 implies 5
	else s=0->1+1->0+2->5 implies 6
	else s=0->1+1->1+2->0 implies 2
	else s=0->1+1->1+2->1 implies 3
	else s=0->1+1->1+2->2 implies 4
	else s=0->1+1->1+2->3 implies 5
	else s=0->1+1->1+2->4 implies 6
	else s=0->1+1->1+2->5 implies 7
	else s=0->1+1->2+2->0 implies 3
	else s=0->1+1->2+2->1 implies 4
	else s=0->1+1->2+2->2 implies 5
	else s=0->1+1->2+2->3 implies 6
	else s=0->1+1->2+2->4 implies 7
	else s=0->1+1->2+2->5 implies 8
	else s=0->1+1->3+2->0 implies 4
	else s=0->1+1->3+2->1 implies 5
	else s=0->1+1->3+2->2 implies 6
	else s=0->1+1->3+2->3 implies 7
	else s=0->1+1->3+2->4 implies 8
	else s=0->1+1->3+2->5 implies 9
	else s=0->1+1->4+2->0 implies 5
	else s=0->1+1->4+2->1 implies 6
	else s=0->1+1->4+2->2 implies 7
	else s=0->1+1->4+2->3 implies 8
	else s=0->1+1->4+2->4 implies 9
	else s=0->1+1->4+2->5 implies 10
	else s=0->1+1->5+2->0 implies 6
	else s=0->1+1->5+2->1 implies 7
	else s=0->1+1->5+2->2 implies 8
	else s=0->1+1->5+2->3 implies 9
	else s=0->1+1->5+2->4 implies 10
	else s=0->1+1->5+2->5 implies 11
	else s=0->2+1->0+2->0 implies 2
	else s=0->2+1->0+2->1 implies 3
	else s=0->2+1->0+2->2 implies 4
	else s=0->2+1->0+2->3 implies 5
	else s=0->2+1->0+2->4 implies 6
	else s=0->2+1->0+2->5 implies 7
	else s=0->2+1->1+2->0 implies 3
	else s=0->2+1->1+2->1 implies 4
	else s=0->2+1->1+2->2 implies 5
	else s=0->2+1->1+2->3 implies 6
	else s=0->2+1->1+2->4 implies 7
	else s=0->2+1->1+2->5 implies 8
	else s=0->2+1->2+2->0 implies 4
	else s=0->2+1->2+2->1 implies 5
	else s=0->2+1->2+2->2 implies 6
	else s=0->2+1->2+2->3 implies 7
	else s=0->2+1->2+2->4 implies 8
	else s=0->2+1->2+2->5 implies 9
	else s=0->2+1->3+2->0 implies 5
	else s=0->2+1->3+2->1 implies 6
	else s=0->2+1->3+2->2 implies 7
	else s=0->2+1->3+2->3 implies 8
	else s=0->2+1->3+2->4 implies 9
	else s=0->2+1->3+2->5 implies 10
	else s=0->2+1->4+2->0 implies 6
	else s=0->2+1->4+2->1 implies 7
	else s=0->2+1->4+2->2 implies 8
	else s=0->2+1->4+2->3 implies 9
	else s=0->2+1->4+2->4 implies 10
	else s=0->2+1->4+2->5 implies 11
	else s=0->2+1->5+2->0 implies 7
	else s=0->2+1->5+2->1 implies 8
	else s=0->2+1->5+2->2 implies 9
	else s=0->2+1->5+2->3 implies 10
	else s=0->2+1->5+2->4 implies 11
	else s=0->2+1->5+2->5 implies 12
	else s=0->3+1->0+2->0 implies 3
	else s=0->3+1->0+2->1 implies 4
	else s=0->3+1->0+2->2 implies 5
	else s=0->3+1->0+2->3 implies 6
	else s=0->3+1->0+2->4 implies 7
	else s=0->3+1->0+2->5 implies 8
	else s=0->3+1->1+2->0 implies 4
	else s=0->3+1->1+2->1 implies 5
	else s=0->3+1->1+2->2 implies 6
	else s=0->3+1->1+2->3 implies 7
	else s=0->3+1->1+2->4 implies 8
	else s=0->3+1->1+2->5 implies 9
	else s=0->3+1->2+2->0 implies 5
	else s=0->3+1->2+2->1 implies 6
	else s=0->3+1->2+2->2 implies 7
	else s=0->3+1->2+2->3 implies 8
	else s=0->3+1->2+2->4 implies 9
	else s=0->3+1->2+2->5 implies 10
	else s=0->3+1->3+2->0 implies 6
	else s=0->3+1->3+2->1 implies 7
	else s=0->3+1->3+2->2 implies 8
	else s=0->3+1->3+2->3 implies 9
	else s=0->3+1->3+2->4 implies 10
	else s=0->3+1->3+2->5 implies 11
	else s=0->3+1->4+2->0 implies 7
	else s=0->3+1->4+2->1 implies 8
	else s=0->3+1->4+2->2 implies 9
	else s=0->3+1->4+2->3 implies 10
	else s=0->3+1->4+2->4 implies 11
	else s=0->3+1->4+2->5 implies 12
	else s=0->3+1->5+2->0 implies 8
	else s=0->3+1->5+2->1 implies 9
	else s=0->3+1->5+2->2 implies 10
	else s=0->3+1->5+2->3 implies 11
	else s=0->3+1->5+2->4 implies 12
	else s=0->3+1->5+2->5 implies 13
	else s=0->4+1->0+2->0 implies 4
	else s=0->4+1->0+2->1 implies 5
	else s=0->4+1->0+2->2 implies 6
	else s=0->4+1->0+2->3 implies 7
	else s=0->4+1->0+2->4 implies 8
	else s=0->4+1->0+2->5 implies 9
	else s=0->4+1->1+2->0 implies 5
	else s=0->4+1->1+2->1 implies 6
	else s=0->4+1->1+2->2 implies 7
	else s=0->4+1->1+2->3 implies 8
	else s=0->4+1->1+2->4 implies 9
	else s=0->4+1->1+2->5 implies 10
	else s=0->4+1->2+2->0 implies 6
	else s=0->4+1->2+2->1 implies 7
	else s=0->4+1->2+2->2 implies 8
	else s=0->4+1->2+2->3 implies 9
	else s=0->4+1->2+2->4 implies 10
	else s=0->4+1->2+2->5 implies 11
	else s=0->4+1->3+2->0 implies 7
	else s=0->4+1->3+2->1 implies 8
	else s=0->4+1->3+2->2 implies 9
	else s=0->4+1->3+2->3 implies 10
	else s=0->4+1->3+2->4 implies 11
	else s=0->4+1->3+2->5 implies 12
	else s=0->4+1->4+2->0 implies 8
	else s=0->4+1->4+2->1 implies 9
	else s=0->4+1->4+2->2 implies 10
	else s=0->4+1->4+2->3 implies 11
	else s=0->4+1->4+2->4 implies 12
	else s=0->4+1->4+2->5 implies 13
	else s=0->4+1->5+2->0 implies 9
	else s=0->4+1->5+2->1 implies 10
	else s=0->4+1->5+2->2 implies 11
	else s=0->4+1->5+2->3 implies 12
	else s=0->4+1->5+2->4 implies 13
	else s=0->4+1->5+2->5 implies 14
	else s=0->5+1->0+2->0 implies 5
	else s=0->5+1->0+2->1 implies 6
	else s=0->5+1->0+2->2 implies 7
	else s=0->5+1->0+2->3 implies 8
	else s=0->5+1->0+2->4 implies 9
	else s=0->5+1->0+2->5 implies 10
	else s=0->5+1->1+2->0 implies 6
	else s=0->5+1->1+2->1 implies 7
	else s=0->5+1->1+2->2 implies 8
	else s=0->5+1->1+2->3 implies 9
	else s=0->5+1->1+2->4 implies 10
	else s=0->5+1->1+2->5 implies 11
	else s=0->5+1->2+2->0 implies 7
	else s=0->5+1->2+2->1 implies 8
	else s=0->5+1->2+2->2 implies 9
	else s=0->5+1->2+2->3 implies 10
	else s=0->5+1->2+2->4 implies 11
	else s=0->5+1->2+2->5 implies 12
	else s=0->5+1->3+2->0 implies 8
	else s=0->5+1->3+2->1 implies 9
	else s=0->5+1->3+2->2 implies 10
	else s=0->5+1->3+2->3 implies 11
	else s=0->5+1->3+2->4 implies 12
	else s=0->5+1->3+2->5 implies 13
	else s=0->5+1->4+2->0 implies 9
	else s=0->5+1->4+2->1 implies 10
	else s=0->5+1->4+2->2 implies 11
	else s=0->5+1->4+2->3 implies 12
	else s=0->5+1->4+2->4 implies 13
	else s=0->5+1->4+2->5 implies 14
	else s=0->5+1->5+2->0 implies 10
	else s=0->5+1->5+2->1 implies 11
	else s=0->5+1->5+2->2 implies 12
	else s=0->5+1->5+2->3 implies 13
	else s=0->5+1->5+2->4 implies 14
	else s=0->5+1->5+2->5 implies 15
	else 0
}

pred sumatoria [s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and sumof[sumaSeq.sec] = suma
}

pred sumatoriaSubSeq [s: set Deposit, suma: Int] {
	some sumaSeq: SumatoriaSeq, subseq: SumatoriaSeq | toSeq[s, sumaSeq.sec] and
			subSeq[sumaSeq.sec, subseq.sec] and sumof[subseq.sec] = suma
}

pred subSeq [original: seq Int, subseq: seq Int] {
	#subseq <= #original
	all i: Int | some subseq[i] implies subseq[i] in original.elems
	all i: Int | some subseq[i] implies #subseq.i <= #original.i
}

pred toSeq [s: set Deposit, ret: seq Int] {
	all d0: s.d.Int | some i: Int | ret[i]=s.d[d0] //Todo elemento del set está en la seq
	all i: Int | some ret[i] implies some d0: s.d.Int | s.d[d0]=ret[i]//Todo elemento de la seq está en el set
	all i: Int | #(s.d.i) = #(ret.i) //#elem(set,e) = #elem(seq,e)
	#(s.d.Int)=#(ret)
}

sig SumatoriaSeq {sec: seq Int}

pred met_constructor [ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, timeElapsed: Int] {
	//Pre
	ein._owner = Address0x0
	ein._admin = Address0x0
	ein._tokensRemaining = 0
	ein._beneficiaryWallet = Address0x0
	ein._amountRaisedInWei = 0
	ein._fundingMinCapInWei = 0
	no ein._currentStatus
	ein._fundingStartBlock = 0
	ein._fundingEndBlock = 0
	ein._isCrowdSaleClosed = False
	ein._areFundsReleasedToBeneficiary = False
	ein._isCrowdSaleSetup = False
	#ein._usersEPXfundValue.d = 0
	ein._balance = 0
	ein._blockNumber >=0
	timeElapsed >= 0




	//Post
	eout._owner = sender
	eout._admin = sender
	eout._currentStatus = CrowdsaleDeployedToChain

	//eout._owner = ein._owner
	//eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	//eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}


pred pre_setupCrowdsale[e: EstadoConcreto] {
	e._isCrowdSaleSetup = False
	e._beneficiaryWallet = Address0x0
}

pred met_setupCrowdsale[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
	fundingStartBlock: Int, fundingEndBlock: Int, value: Int, timeElapsed: Int] {
	//PRE
	pre_setupCrowdsale [ein]
	ein._owner = sender
	ein._admin = sender
	fundingStartBlock >=0 and fundingEndBlock>=0
	timeElapsed >= 0

	
	//POST
	eout._beneficiaryWallet = AddressBene0x7A29e
	eout._fundingMinCapInWei = 3
	eout._amountRaisedInWei = 0
	eout._tokensRemaining = 6
	eout._fundingStartBlock = fundingStartBlock
	eout._fundingEndBlock = fundingEndBlock
	eout._isCrowdSaleSetup = True
	eout._isCrowdSaleClosed = False
	eout._currentStatus = CrowdsaleIsSetup

	eout._owner = ein._owner
	eout._admin = ein._admin
	//eout._tokensRemaining = ein._tokensRemaining
	//eout._beneficiaryWallet = ein._beneficiaryWallet
	//eout._amountRaisedInWei = ein._amountRaisedInWei
	//eout._fundingMinCapInWei = ein._fundingMinCapInWei
	//eout._currentStatus = ein._currentStatus
	//eout._fundingStartBlock = ein._fundingStartBlock
	//eout._fundingEndBlock = ein._fundingEndBlock
	//eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	//eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}

/*
pred pre_setupCrowdsaleRetNotAuthorised[e: EstadoConcreto] {
	not pre_setupCrowdsale[e]
}

pred setupCrowdsaleRetNotAuthorised[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
	fundingStartBlock: Int, fundingEndBlock: Int, value: Int, timeElapsed: Int] {
	//PRE
	pre_setupCrowdsaleRetNotAuthorised[ein]
	ein._owner = sender // porque hay un modifier
	ein._admin != sender
	timeElapsed >= 0

	//POST

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}
*/

/*
pred pre_setupCrowdsaleCampCantChange[e: EstadoConcreto] {
	not pre_setupCrowdsale[e]
}

pred setupCrowdsaleCampCantChange[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address,
	fundingStartBlock: Int, fundingEndBlock: Int, value: Int, timeElapsed: Int] {
	//PRE
	pre_setupCrowdsaleCampCantChange[ein]
	ein._owner = sender
	ein._admin = sender
	timeElapsed >= 0

	//POST

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}
*/

fun checkPrice[e:EstadoConcreto]: Int {
	//e._blockNumber >= fundingStartBlock+177534 implies 7600
    	//e._block.number >= fundingStartBlock+124274 implies 8200
	//e._block.number >= fundingStartBlock implies 8800
	
	e._blockNumber >= e._fundingStartBlock.add[2] implies 1
	else e._blockNumber >= e._fundingStartBlock.add[1] implies 2
	else e._blockNumber >= e._fundingStartBlock implies 3
	else 0
}



pred pre_buy[e: EstadoConcreto] {
	e._blockNumber <= e._fundingEndBlock
	e._blockNumber >= e._fundingStartBlock
	e._tokensRemaining > 0
}

pred met_buy[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value:Int, timeElapsed: Int] {
	//PRE
	pre_buy[ein]
	value > 0
	ein._usersEPXfundValue.d[sender].add[value] <= LIMIT[]
	timeElapsed >= 0
	
	
	//POST
	eout._amountRaisedInWei = ein._amountRaisedInWei.add[value]
	eout._usersEPXfundValue.d = ein._usersEPXfundValue.d++sender->ein._usersEPXfundValue.d[sender].add[value]
	//let rewardTransferAmount = (value.mul[checkPrice[ein]).div[100000000000000] |
	
	//let rewardTransferAmount = value.mul[checkPrice[ein]] |
	let rewardTransferAmount = value.add[checkPrice[ein]] |
		eout._tokensRemaining = ein._tokensRemaining.sub[rewardTransferAmount]
		//tokenReward.transfer(msg.sender, rewardTransferAmount);
		
	
	eout._owner = ein._owner
	eout._admin = ein._admin
	//eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	//eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	//eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}



pred pre_checkGoalReached[e: EstadoConcreto] {
	e._isCrowdSaleSetup = True
}

pred met_checkGoalReached[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, timeElapsed: Int] {
	//PRE
	pre_checkGoalReached[ein]
	ein._owner = sender
	timeElapsed >= 0
	
	//POST
	(ein._amountRaisedInWei < ein._fundingMinCapInWei and ein._blockNumber <= ein._fundingEndBlock
	and ein._blockNumber >= ein._fundingStartBlock) // ICO in progress, under softcap
		=> (eout._areFundsReleasedToBeneficiary = False and eout._isCrowdSaleClosed = False
			and eout._currentStatus = InProgress_Eth_low_Softcap)
	else (ein._amountRaisedInWei < ein._fundingMinCapInWei and ein._blockNumber < ein._fundingStartBlock) // ICO has not started
     		=> (eout._areFundsReleasedToBeneficiary = False and eout._isCrowdSaleClosed = False
			and eout._currentStatus = CrowdsaleIsSetup)
	else (ein._amountRaisedInWei < ein._fundingMinCapInWei and ein._blockNumber > ein._fundingEndBlock) // ICO ended, under softcap
		=> eout._areFundsReleasedToBeneficiary = False and eout._isCrowdSaleClosed = True
			and eout._currentStatus = Unsuccessful_Eth_low_Softcap
	else (ein._amountRaisedInWei >= ein._fundingMinCapInWei and ein._tokensRemaining = 0) // ICO ended, all tokens bought!
		=> (eout._areFundsReleasedToBeneficiary = True and eout._isCrowdSaleClosed = True
			and eout._currentStatus = Successful_EPX_ge_Hardcap)
	else (ein._amountRaisedInWei >= ein._fundingMinCapInWei and ein._blockNumber > ein._fundingEndBlock
	and ein._tokensRemaining > 0) // ICO ended, over softcap!
		=> (eout._areFundsReleasedToBeneficiary = True and eout._isCrowdSaleClosed = True
			and eout._currentStatus = Successful_Eth_ge_Softcap)
	else (ein._amountRaisedInWei >= ein._fundingMinCapInWei and ein._tokensRemaining > 0
	and ein._blockNumber <= ein._fundingEndBlock) // ICO in progress, over softcap!
		=> (eout._areFundsReleasedToBeneficiary = True and eout._isCrowdSaleClosed = False
			and eout._currentStatus = InProgress_Eth_ge_Softcap)
	else eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
		and eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
		and eout._currentStatus = ein._currentStatus

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	//eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	//eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	//eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}


pred pre_refund[e: EstadoConcreto] {
	e._amountRaisedInWei < e._fundingMinCapInWei
	e._isCrowdSaleClosed = True
	e._blockNumber > e._fundingEndBlock
	some a:Address | e._usersEPXfundValue.d[a] > 0
}

pred met_refund[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, timeElapsed: Int] {
	//PRE
	pre_refund[ein]
	ein._usersEPXfundValue.d[sender] > 0
	timeElapsed >= 0
	
	//POST
	eout._usersEPXfundValue.d = ein._usersEPXfundValue.d++sender->0

	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	//eout._usersEPXfundValue = ein._usersEPXfundValue
	//eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._blockNumber = ein._blockNumber
	eout._balance = ein._balance
}

pred pre_t[e:EstadoConcreto] {
}

pred met_t[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, value: Int, timeElapsed: Int] {
	//PRE
	timeElapsed >= 0
	
	eout._owner = ein._owner
	eout._admin = ein._admin
	eout._tokensRemaining = ein._tokensRemaining
	eout._beneficiaryWallet = ein._beneficiaryWallet
	eout._amountRaisedInWei = ein._amountRaisedInWei
	eout._fundingMinCapInWei = ein._fundingMinCapInWei
	eout._currentStatus = ein._currentStatus
	eout._fundingStartBlock = ein._fundingStartBlock
	eout._fundingEndBlock = ein._fundingEndBlock
	eout._isCrowdSaleClosed = ein._isCrowdSaleClosed
	eout._areFundsReleasedToBeneficiary = ein._areFundsReleasedToBeneficiary
	eout._isCrowdSaleSetup = ein._isCrowdSaleSetup
	eout._usersEPXfundValue = ein._usersEPXfundValue
	eout._blockNumber = ein._blockNumber.add[timeElapsed]
	eout._balance = ein._balance
}


//////////////////////////////////////////////////////////////////////////////////////
// agrego un predicado por cada partición teórica posible //
//////////////////////////////////////////////////////////////////////////////////////

pred partitionS00[e: EstadoConcreto]{
	//(invariante[e])
	e._owner = Address0x0
	e._admin = Address0x0
	e._tokensRemaining = 0
	e._beneficiaryWallet = Address0x0
	e._amountRaisedInWei = 0
	e._fundingMinCapInWei = 0
	no e._currentStatus
	e._fundingStartBlock = 0
	e._fundingEndBlock = 0
	e._isCrowdSaleClosed = False
	e._areFundsReleasedToBeneficiary = False
	e._isCrowdSaleSetup = False
	#e._usersEPXfundValue.d = 0
	e._balance = 0
	e._blockNumber >=0
}

run partitionS00

pred partitionINV[e: EstadoConcreto]{
	not invariante[e]
}


pred partitionS01[e:EstadoConcreto] {
	(invariante[e])
	e._currentStatus = CrowdsaleDeployedToChain
}

pred partitionS02[e:EstadoConcreto] {
	(invariante[e])
	e._currentStatus = CrowdsaleIsSetup
}

pred partitionS03[e:EstadoConcreto] {
	(invariante[e])
	e._currentStatus = InProgress_Eth_low_Softcap
}

pred partitionS04[e:EstadoConcreto] {
	(invariante[e])
	e._currentStatus = InProgress_Eth_ge_Softcap
}

pred partitionS05[e:EstadoConcreto] {
	(invariante[e])
	e._currentStatus = Unsuccessful_Eth_low_Softcap
}

pred partitionS06[e:EstadoConcreto] {
	(invariante[e])
	e._currentStatus = Successful_EPX_ge_Hardcap
}

pred partitionS07[e:EstadoConcreto] {
	(invariante[e])
	e._currentStatus = Successful_Eth_ge_Softcap
}






pred transicion_S00_a_S01_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S02_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S03_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S04_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S05_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S06_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_S07_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S00_a_INV_mediante_met_constructor {
	(partitionS00[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_constructor  [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S00_a_S01_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S02_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S03_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S04_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S05_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S06_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_S07_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S00_a_INV_mediante_met_constructor  for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S01_a_S02_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S01_a_S03_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S01_a_S04_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S01_a_S05_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S01_a_S06_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S01_a_S07_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S01_a_INV_mediante_met_setupCrowdsale{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_S01_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_S02_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_S03_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_S04_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_S05_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_S06_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_S07_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S02_a_INV_mediante_met_setupCrowdsale{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_S01_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_S02_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_S03_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_S04_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_S05_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_S06_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_S07_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S03_a_INV_mediante_met_setupCrowdsale{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_S01_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_S02_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_S03_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_S04_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_S05_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_S06_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_S07_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S04_a_INV_mediante_met_setupCrowdsale{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_S01_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_S02_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_S03_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_S04_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_S05_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_S06_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_S07_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S05_a_INV_mediante_met_setupCrowdsale{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_S01_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_S02_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_S03_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_S04_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_S05_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_S06_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_S07_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S06_a_INV_mediante_met_setupCrowdsale{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_S01_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_S02_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_S03_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_S04_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_S05_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_S06_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_S07_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

pred transicion_S07_a_INV_mediante_met_setupCrowdsale{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21, v22, v23:Int | v10 != Address0x0 and met_setupCrowdsale [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21, v22, v23])
}

run transicion_S01_a_S01_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_INV_mediante_met_setupCrowdsale for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S02_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S03_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S04_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S05_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S06_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_S07_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S01_a_INV_mediante_met_buy{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S01_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S02_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S03_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S04_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S05_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S06_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_S07_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S02_a_INV_mediante_met_buy{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S01_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S02_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S03_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S04_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S05_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S06_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_S07_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S03_a_INV_mediante_met_buy{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S01_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S02_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S03_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S04_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S05_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S06_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_S07_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S04_a_INV_mediante_met_buy{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S01_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S02_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S03_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S04_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S05_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S06_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_S07_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S05_a_INV_mediante_met_buy{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S01_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S02_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S03_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S04_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S05_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S06_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_S07_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S06_a_INV_mediante_met_buy{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S01_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S02_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S03_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S04_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S05_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S06_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_S07_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

pred transicion_S07_a_INV_mediante_met_buy{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_buy [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_INV_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_INV_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_INV_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_INV_mediante_met_buy for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S06_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S07_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_checkGoalReached{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S06_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S07_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_checkGoalReached{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S06_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S07_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_checkGoalReached{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S06_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S07_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_checkGoalReached{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S06_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S07_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_checkGoalReached{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S01_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S02_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S03_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S04_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S05_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S06_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S07_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_INV_mediante_met_checkGoalReached{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S01_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S02_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S03_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S04_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S05_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S06_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S07_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_INV_mediante_met_checkGoalReached{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_checkGoalReached [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S01_a_S01_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_INV_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_INV_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_INV_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_INV_mediante_met_checkGoalReached for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
pred transicion_S01_a_S01_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S02_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S03_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S04_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S05_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S06_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_S07_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S01_a_INV_mediante_met_refund{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S01_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S02_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S03_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S04_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S05_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S06_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_S07_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S02_a_INV_mediante_met_refund{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S01_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S02_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S03_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S04_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S05_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S06_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_S07_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S03_a_INV_mediante_met_refund{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S01_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S02_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S03_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S04_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S05_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S06_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_S07_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S04_a_INV_mediante_met_refund{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S01_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S02_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S03_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S04_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S05_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S06_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_S07_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S05_a_INV_mediante_met_refund{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S01_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S02_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S03_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S04_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S05_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S06_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_S07_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S06_a_INV_mediante_met_refund{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S01_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionS01[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S02_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionS02[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S03_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionS03[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S04_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionS04[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S05_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionS05[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S06_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionS06[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_S07_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionS07[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

pred transicion_S07_a_INV_mediante_met_refund{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20:Int | v10 != Address0x0 and met_refund [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20])
}

run transicion_S01_a_S01_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_INV_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_INV_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_INV_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_INV_mediante_met_refund for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
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

pred transicion_S01_a_INV_mediante_met_t{
	(partitionS01[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
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

pred transicion_S02_a_INV_mediante_met_t{
	(partitionS02[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
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

pred transicion_S03_a_INV_mediante_met_t{
	(partitionS03[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
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

pred transicion_S04_a_INV_mediante_met_t{
	(partitionS04[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
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

pred transicion_S05_a_INV_mediante_met_t{
	(partitionS05[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
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

pred transicion_S06_a_INV_mediante_met_t{
	(partitionS06[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
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

pred transicion_S07_a_INV_mediante_met_t{
	(partitionS07[EstadoConcretoInicial])
	(partitionINV[EstadoConcretoFinal])
	(some v10:Address, v20, v21:Int | v10 != Address0x0 and met_t [EstadoConcretoInicial, EstadoConcretoFinal, v10, v20, v21])
}

run transicion_S01_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S01_a_INV_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S02_a_INV_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S03_a_INV_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S04_a_INV_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S05_a_INV_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S06_a_INV_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S01_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S02_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S03_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S04_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S05_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S06_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_S07_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
run transicion_S07_a_INV_mediante_met_t for 2 EstadoConcreto, 2 Deposit, 2 SumatoriaSeq
