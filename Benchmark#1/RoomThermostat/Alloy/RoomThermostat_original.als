// atomos: estados de la máquina de estado
abstract sig EstadoAbstracto{transiciones: Accion -> set EstadoAbstracto}
one sig A0 extends EstadoAbstracto{}
one sig A1 extends EstadoAbstracto{}


//Acciones de los estados abstractos
abstract sig Accion{}
one sig AccionConstructor extends Accion {}
one sig AccionStartThermostat extends Accion {}
one sig AccionSetTargetTemperature extends Accion {}
one sig AccionSetMode extends Accion {}

// Describo cómo pasar de un estado a otro mediante cada acción
fact trans_accionConstructor{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionConstructor]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10,v11,v12:Address | constructor[e0,e1,v10,v11,v12]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionStartThermostat{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionStartThermostat]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address | startThermostat[e0,e1,v10]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionSetTargetTemperature{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionSetTargetTemperature]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Int | setTargetTemperature[e0,e1,v10,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }

fact trans_accionSetMode{all a0,a1:EstadoAbstracto | a1 in a0.transiciones[AccionSetMode]
	iff (some e0:EstadoConcretoInicial,e1:EstadoConcretoFinal,v10:Address,v20:Mode | setMode[e0,e1,v10,v20]
	and FnAbstraccion.F[e0] = a0 and FnAbstraccion.F[e1] = a1) }


// Declaro fn de abstracción que relaciona estado concreto con estado abstracto
one sig FnAbstraccion{F: EstadoConcreto -> one EstadoAbstracto}

// estados concretos
abstract sig Address{}
one sig Address0 extends Address{}
one sig Address1 extends Address{}
one sig Address2 extends Address{}
one sig Address3 extends Address{}
one sig Address4 extends Address{}
one sig Address5 extends Address{}

abstract sig EstadoContrato{}
one sig Created extends EstadoContrato{}
one sig InUse extends EstadoContrato{}

abstract sig Mode{}
one sig Off extends Mode{}
one sig Cool extends Mode{}
one sig Heat extends Mode{}
one sig Auto extends Mode{}

abstract sig EstadoConcreto {
	_installer: lone Address,
	_user: lone Address,
	_targetTemperature: lone Int,
	_mode: lone Mode,
	_state: lone EstadoContrato
}

one sig EstadoConcretoInicial extends EstadoConcreto{}
one sig EstadoConcretoFinal extends EstadoConcreto{}


pred invariante[e:EstadoConcreto] {
	//Address con nombre diferente
	//(no disj a1,a2:Address | a1.name = a2.name)
}


pred constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, thermostatInstaller: Address, thermostatUser:Address] {
	//Pre
	(no ein._state and no ein._installer and no ein._user and no ein._targetTemperature and no ein._mode
	 and no ein._state)
	//Post
	eout._installer = thermostatInstaller
	eout._user = thermostatUser
	eout._targetTemperature = 4

	//eout._installer = ein._installer
	//eout._user = ein._user
	//eout._targetTemperature = ein._targetTemperature
	eout._mode = ein._mode
	eout._state = ein._state
}

pred startThermostat[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	some ein._state
	not(ein._installer != sender or ein._state != Created)

	//Post
        eout._state = InUse

	eout._installer = ein._installer
	eout._user = ein._user
	eout._targetTemperature = ein._targetTemperature
	eout._mode = ein._mode
	//eout._state = ein._state
}

pred setTargetTemperature[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, targetTemperature: Int] {
	//Pre
	some ein._state
	not (ein._user != sender or ein._state != InUse)

	//Post
	eout._targetTemperature = targetTemperature

	eout._installer = ein._installer
	eout._user = ein._user
	//eout._targetTemperature = ein._targetTemperature
	eout._mode = ein._mode
	eout._state = ein._state
}

pred setMode[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, mode: Mode] {
	//Pre	
	some ein._state
	not  (ein._user != sender or  ein._state != InUse)
	
	//Post
	eout._mode = mode

	eout._installer = ein._installer
	eout._user = ein._user
	eout._targetTemperature = ein._targetTemperature
	//eout._mode = ein._mode
	eout._state = ein._state
}


// agrego un predicado por cada partición teórica posible
pred particionS00[e: EstadoConcreto]{ // 
	(invariante[e])
	no e._state
}

pred particionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Created
}

pred particionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = InUse
}

pred particionINV[e: EstadoConcreto]{ // 
	not (invariante[e])
}

// agregar un predicado para cada transición posible
/*
De S0 a SN con acción
*/
pred transicion_S00_a_S00_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S00_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S01_a_S01_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_S02_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S01_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


pred transicion_S02_a_S02_mediante_constructor{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S00_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_S01_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}

pred transicion_S02_a_INV_mediante_constructor{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionConstructor])
}


run transicion_S00_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address

run transicion_S01_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address

run transicion_S02_a_S02_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_constructor for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_constructor for 2 EstadoConcreto, 5 Address

pred transicion_S00_a_S00_mediante_startThermostat{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S00_a_S01_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S00_a_S02_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S00_a_INV_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}


pred transicion_S01_a_S01_mediante_startThermostat{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S01_a_S00_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S01_a_S02_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S01_a_INV_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}


pred transicion_S02_a_S02_mediante_startThermostat{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S02_a_S00_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S02_a_S01_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}

pred transicion_S02_a_INV_mediante_startThermostat{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionStartThermostat])
}


run transicion_S00_a_S00_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_startThermostat for 2 EstadoConcreto, 5 Address

run transicion_S01_a_S01_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_startThermostat for 2 EstadoConcreto, 5 Address

run transicion_S02_a_S02_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_startThermostat for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_startThermostat for 2 EstadoConcreto, 5 Address

pred transicion_S00_a_S00_mediante_setTargetTemperature{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S00_a_S01_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S00_a_S02_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S00_a_INV_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}


pred transicion_S01_a_S01_mediante_setTargetTemperature{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S01_a_S00_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S01_a_S02_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S01_a_INV_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}


pred transicion_S02_a_S02_mediante_setTargetTemperature{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S02_a_S00_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S02_a_S01_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}

pred transicion_S02_a_INV_mediante_setTargetTemperature{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetTargetTemperature])
}


run transicion_S00_a_S00_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address

run transicion_S01_a_S01_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address

run transicion_S02_a_S02_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_setTargetTemperature for 2 EstadoConcreto, 5 Address

pred transicion_S00_a_S00_mediante_setMode{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS00[e]))
	(A0 in A0.transiciones[AccionSetMode])
}

pred transicion_S00_a_S01_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}

pred transicion_S00_a_S02_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}

pred transicion_S00_a_INV_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS00[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}


pred transicion_S01_a_S01_mediante_setMode{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS01[e]))
	(A0 in A0.transiciones[AccionSetMode])
}

pred transicion_S01_a_S00_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}

pred transicion_S01_a_S02_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS02[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}

pred transicion_S01_a_INV_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS01[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}


pred transicion_S02_a_S02_mediante_setMode{
	(all e:EstadoConcreto | FnAbstraccion.F[e] = A0 iff (particionS02[e]))
	(A0 in A0.transiciones[AccionSetMode])
}

pred transicion_S02_a_S00_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS00[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}

pred transicion_S02_a_S01_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionS01[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}

pred transicion_S02_a_INV_mediante_setMode{
	(FnAbstraccion.F[EstadoConcretoInicial] = A0 and (particionS02[EstadoConcretoInicial]))
	(FnAbstraccion.F[EstadoConcretoFinal] = A1 and (particionINV[EstadoConcretoFinal]))
	(A1 in A0.transiciones[AccionSetMode])
}


run transicion_S00_a_S00_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S01_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S00_a_S02_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S00_a_INV_mediante_setMode for 2 EstadoConcreto, 5 Address

run transicion_S01_a_S01_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S00_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S01_a_S02_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S01_a_INV_mediante_setMode for 2 EstadoConcreto, 5 Address

run transicion_S02_a_S02_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S00_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S02_a_S01_mediante_setMode for 2 EstadoConcreto, 5 Address
run transicion_S02_a_INV_mediante_setMode for 2 EstadoConcreto, 5 Address
