// ALLOY SPECIFICATION 
// FOR CARSHARING SYSTEM RASD
// AUTHOR: ARTEMIY FROLOV

// PEOPLE
// ============================================================================

// Any person
abstract sig Person{}
// Registered User
sig RegUser extends Person {
payment: lone Payment
} 
// Unregistered User
sig UnReg extends Person {}



/*
fact UsersWithoutTheCarCannotHavePayment {
all c: Car | all r: RegUser | (r not in c.wastakenby) implies (no r.payment)  
}
*/


// PAYMENT
// ============================================================================
// Discounts
abstract sig Discount {}
sig Discount10Percent extends Discount {}
sig Discount20Percent extends Discount {}
sig Discount30Percent extends Discount {}
abstract sig Charge {}
sig Euro1 extends Charge{} 

sig Payment {
discounts: Discount,
charges: Charge
} {
#discounts >= 0
#charges >= 0
}


// PARKING
// ============================================================================
abstract sig Parked {}
sig SpecialParkingArea extends Parked{}
sig AnyParkingArea extends Parked {}
sig Driven extends Parked{}


// TIME
// ============================================================================
abstract sig Time {}
sig Less1h extends Time{}
sig More1h extends Time{}

// CAR
// ============================================================================

// Car occupation states
abstract sig CarOccupationState {}
sig Available extends CarOccupationState {}
sig Reserved extends CarOccupationState {}
sig Occupied extends CarOccupationState {}
sig Released extends CarOccupationState {}
sig LostReservation extends CarOccupationState {}
sig LostOccupation extends CarOccupationState {}

// Car charging states
abstract sig CarChargingState {}
sig Charging extends CarChargingState {}
sig NotCharging extends CarChargingState {}

// Battery fulness
abstract sig BatteryFulness {}
sig More50 extends BatteryFulness {}
sig Less20 extends BatteryFulness {}
sig More20Less50 extends BatteryFulness {}

// Engine State
abstract sig CarEngineState {}
sig EngineOn extends CarEngineState {}
sig EngineOff extends CarEngineState {}

// Car
sig Car {
occupationstate: one CarOccupationState, // wether car is available, reserved, occupied or released
chargingstate: one CarChargingState, // wether car is charging or not 
takenby: lone RegUser, // car can either have a RegUser or not
wastakenby: lone RegUser, // 
passengers: set Person, // can carry some persons
hadpassengers: set Person,
battery: one BatteryFulness, // battery fulness
parked: one Parked,
enginestate: one CarEngineState,
reservationtime: lone Time
}{
#passengers >= 0
#passengers <= 4
#hadpassengers >= 0
#hadpassengers <= 4
}


// CONVENTIONS
// ============================================================================


// OK
fact NoUserCanUseTheSameCar {
all c1, c2: Car | ((c1 != c2) and (c1.takenby != none) and (c1.takenby != none)) implies (c1.takenby != c2.takenby)
}

// OK
fact NoTheSamePassengers {
all c1, c2: Car | (c1 != c2) implies (c1.passengers & c2.passengers) = none
all c1, c2: Car | (c1 != c2) implies (c1.hadpassengers & c2.hadpassengers) = none
all c1, c2: Car | (c1 != c2) implies (c1.takenby not in c2.passengers)
all c1, c2: Car | (c1 != c2) implies (c1.wastakenby not in c2.hadpassengers)
}

// occupationstate: one CarOccupationState, // wether car is available, reserved, occupied or released
/* Available state implies:
1. no RegUser in Car.takenby, no passengers
2. must be parked
3. can be charged
4. no reservationtime
5. no payment
6. Engine is off ahahah
*/
fact CarIsAvailableConventions {
all c: Car | (c.occupationstate = Available) implies
(
//no c.takenby
no c.takenby and
no c.wastakenby and
no c.passengers and
no c.hadpassengers and
c.parked != Driven and
no c.reservationtime
)}

/*
assert AvailabilityConventions {
	no c: Car | c.occupationstate = Available and
	(
		c.takenby != none or
		c.wastakenby != none or
		c.passengers != none or
		c.hadpassengers != none or
		c.parked = Driven or
		c.reservationtime != none
	)
}
*/
/* Reserved state implies:
1.1. RegUser in Car.takenby, 
1.2. no passengers. It means that Car.takenby has RegUser, but neither RegUser is in Car.passengers nor any other Person
2. must be parked
3. can be charged
4.1. reservation time must be set. 
5. User don't have payment
6. engine off
*/

fact CarIsReservedConventions {
all c: Car | (c.occupationstate = Reserved) implies (
c.takenby != none and 
no c.wastakenby and 
no c.passengers and 
no c.hadpassengers and
c.parked != Driven and
c.reservationtime = Less1h
)}

/*
assert ReservationConventions {
all c: Car | (c.occupationstate = Reserved) implies (
c.takenby != none or
no c.wastakenby or
no c.passengers or
no c.hadpassengers or
c.parked != Driven or 
c.reservationtime = Less1h
)}
*/
//check ReservationConventions


/*LostReservation state implies
1.1. No RegUser in Car.takenby
1.2. No passengers
2. Engine must be off
3. reservationtime must be More1h
4. User must have payment 1 euro
*/

fact CarIsLostReservationConventions {
all c: Car | (c.occupationstate = LostReservation) implies (
(no c.takenby) and 
(c.wastakenby != none) and
(no c.passengers) and
(no c.hadpassengers) and
(c.enginestate = EngineOff) and
(c.reservationtime = More1h) and
(c.wastakenby.payment.charges = c.wastakenby.payment.charges + Euro1)
)}

/*
assert LostReservationConventions {
all c: Car | (c.occupationstate = LostReservation) implies (
(no c.takenby) or 
(c.wastakenby != none) or
(no c.passengers) or
(no c.hadpassengers) or
(c.enginestate = EngineOff) or
(c.reservationtime = More1h) or
(c.wastakenby.payment.charges = c.wastakenby.payment.charges + Euro1)
)}
*/
//check LostReservationConventions 

/* Occupied state implies:
1.1. RegUser in Car.takenby, 
1.2. can be passengers.
2. can be driven or parked
3. can be charged
4. no reservationtime
5. User don't have payment
*/

fact CarIsOccupiedConventions {
all c: Car | (c.occupationstate = Occupied) implies (
(c.takenby != none) and
(no c.hadpassengers) and
(no c.reservationtime) and 
(no c.wastakenby)
)}

/*
assert OccupiedConventions {
all c: Car | (c.occupationstate = Occupied) implies (
(c.takenby != none) or
(no c.hadpassengers) or
(no c.reservationtime) or
(no c.wastakenby)
)}
*/
//check OccupiedConventions

/*LostOccupation state implies
1.1 no RegUser in Car.takenby. 
1.2. Can be any passengers
2. Can be charged
3. 
USer must have payment
*/

fact CarIsLostOccupationConventions {
all c: Car | (c.occupationstate = LostOccupation) implies (
(no c.takenby) and
(c.wastakenby != none) and
(no c.passengers) and
(c.hadpassengers != none) and
(c.enginestate = EngineOff) and 
(c.reservationtime = More1h) and
(c.wastakenby.payment != none)
)}
/*
assert LostOccupationConventions {
all c: Car | (c.occupationstate = LostOccupation) implies (
(no c.takenby) or
(c.wastakenby != none) or
(no c.passengers) or
(c.hadpassengers != none) or
(c.enginestate = EngineOff) or
(c.reservationtime = More1h) or
(c.wastakenby.payment != none)
)}
*/
//check LostOccupationConventions 



/* Released state implies:
1. no RegUser in Car.takenby, no passengers
2. engine is off
3. can be charged
4. User must have payment
5. no time
*/

fact CarIsReleasedConventions {
all c: Car |  (c.occupationstate = Released) implies (
(no c.takenby) and 
(c.takenby != none) and
(c.enginestate = EngineOff) and
(no c.passengers) and
(c.wastakenby.payment != none) and
(no c.reservationtime)
)}



//chargingstate: one CarChargingState, // wether car is charging or not 
/* Charging state:
1. <=> car is parked
*/


fact CarChargingConventions {
all c: Car | (c.chargingstate = Charging) implies (c.parked != Driven)
}



/* NotCharging state:
1. car can be either parked or driving
*/
// NO NEED TO IMPLEMENT



//takenby: lone RegUser, // car can either have a RegUser or not
/*
1. user != non implies states
*/


/*
fact TakenByConvention {
all c: Car | (no c.takenby) implies {
(c.occupationstate = Available) or (c.occupationstate = LostReservation) or (c.occupationstate = LostOccupation)
}}
*/

//passengers: some Person, // can carry some persons
/*
*/


//battery: one BatteryFulness, // battery fulness
/*
1. number of batteries must be equal to number of cars
*/

//parked: one Parked,
/*
AnyParkingArea:
1. 
*/ 

/*
SpecialParkingArea:
1. && Car.chargingstate = Charging => see REQUIREMENTS
*/ 




/*
Driving:
1. must have at least 1 passenger - RegUser
2. Car must be occupied 
3. NotCharging state
4. What about 2 passengers?
5. Engine must be on
*/ 

// ___________________________________
/*
fact CarIsDrivenConventions {
all c: Car | (c.parked = Driven) implies {
//1.
c.takenby != none
c.takenby in c.passengers
//2.
c.occupationstate = Occupied
//3.
c.chargingstate = NotCharging
//4.
// ????
//5.
c.enginestate = EngineOn
}}
*/

// enginestate: one CarEngineState
/*
EngineOn:
1. Car must be occupied
*/ 
/*
EngineOff:
1. must be parked
*/



fact CarEngineConventions {
all c: Car | (c.enginestate = EngineOn) implies {
//1.
c.occupationstate = Occupied
} else {
//1.
c.parked != Driven
}}



/* MERGED INTO ONE ABOVE
fact CarEngineOffConventions {
all c: Car | c.enginestate = EngineOff implies {
//1.
c.parked != Driven
}}
*/

//reservationtime: lone Time
/* Less1h:
1. <=> EngineOff && Occupied || Reserved
2. passengers can either be in the car or not
*/ 

// __________________________________________________
/*
fact CarLess1hTimeConventions {
all c:Car | (c.reservationtime = Less1h) implies {
(c.enginestate = EngineOff) and // to run a countdown engine must be off
((c.occupationstate = Occupied) or (c.occupationstate = Reserved))
}}
*/

/* More1h:
1. <=> EngineOff && LostResevation || LostOccupation
2. passengers can either be in the car or not
*/ 
//_________________________________
/*
fact CarMore1hTimeConventions {
all c:Car | (c.reservationtime = More1h) implies {
((c.enginestate = EngineOff) and ((c.occupationstate = LostOccupation) or (c.occupationstate = LostReservation)))
}}
*/


fact TakenWasTakenConventions {
all c: Car | (#c.takenby > 0) implies (#c.wastakenby = 0)
or
all c: Car | (#c.wastakenby > 0) implies (#c.takenby = 0)
or
all c: Car | (#c.passengers > 0) implies (#c.hadpassengers = 0)
or
all c: Car | (#c.hadpassengers > 0) implies (#c.passengers = 0)
}

/*
fact PassengersConvention {
//all p: Car.passengers | 

}
*/


/*
fact NumberOfPersonsInTheCar {
all c: Car { 
// NOTE: Number of RegUsers is restricted in Car definition
c.takenby != none implies #c.passengers <= 4 else // If the car is taken by RegUser, it can take at most 4 persons more
#c.passengers = 0 // if car is not taken by RegUser, no one can be in the car 
}}
*/
// ============================================================================

// ENCOURAGEMENT
// ============================================================================

// 2 passengers discount????
fact More2PassengersDiscount {
all c: Car, oc: c.occupationstate, p: Payment | (((oc = Released) or (oc = LostOccupation)) && (#c.hadpassengers >= 3)) implies p.discounts = (p.discounts + Discount10Percent)     
}
// 50% full battery discount
fact More50PercentEnergyDiscount{
all c: Car, oc: c.occupationstate, p: Payment | ((( oc = Released) or (oc = LostOccupation) or (oc = LostReservation)) && (c.battery = More50)) implies p.discounts = (p.discounts + Discount20Percent)
}
// Charging on the special parking zone discount
fact ChargingOfTheCarDiscount {
all c: Car, oc: c.occupationstate, p: Payment | ((( oc = Released) or (oc = LostOccupation) or (oc = LostReservation)) && (c.chargingstate = Charging) && (c.parked = SpecialParkingArea)) implies p.discounts = (p.discounts + Discount30Percent) // We suppose that charging of the car can only be done on the special parking area
//
}

// ============================================================================

pred show () {
//Car.occupationstate = LostReservation
some c: Car | c.occupationstate = LostReservation
//Car.occupationstate = Released
}


//check TakenBy
run show for 10
