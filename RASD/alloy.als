// === PRIMITIVE SIGNATURES ===
sig Name {}

sig Surname {}

sig Email {}

sig Address {}

sig Double {}

enum Bool {
	True,
	False
	}


// === SIGNATURES ===
sig Time {
	value: Int
	} { value >= 0 }

sig Date {
	value: Int
	} { value >= 0 }

sig Ride {
	makeUseTicket: lone Ticket,
	byTranMean: TransportationMean,
	fromLocation: Location,
	toLocation: Location
	}	{ fromLocation != toLocation }

sig TransportationCompany {}

abstract sig Ticket {
	usedFor: some TransportationMean,
	providedByCompany: TransportationCompany
	}

sig User {
	name: Name,
	surname: Surname,
	email: Email,
	ownsTicket: set Ticket,
	hasPreferences: Preferences,
	hasConstraints: set TransportationMeanConstraint,
	speaksLanguage: Language,
	setBreakWindows: set BreakWindow,
	createsAppointment: set Appointment,
	partecipatesToAppointment: set Appointment,
	hasTravelPlan: set TravelPlan,
	currentlyAtLoc: Location
	}

sig Appointment {
	start: Time,
	end: Time, 
	atLocation: Location,
	hasType: AppointmentType,
	isRepeatable: lone RepeatableAppointment
	}

sig Location {
	address: Address,
	latitude: Double,
	longitude: Double
	}

enum AppointmentType {
	Personal,
	Work
	}

sig RepeatableAppointment {
	every: Int,
	start: Date, 
	end: Date
	} { every > 0 
		   start.value < end.value }

sig TravelPlan {
	passengers: Int,
	baggage: Int,
	hasRide: some Ride,
	forAppointment: Appointment
	} { passengers >= 0 
		   baggage >= 0 }

abstract sig BreakWindow {}

sig FixedBreakWindow extends BreakWindow {
	from: Time,
	to: Time
	} { from.value < to.value }

sig FlexibleBreakWindow extends BreakWindow {
	from: Time,
	to: Time,
	atLeast: Time
	} { from.value < to.value
		  atLeast.value > 0 }

enum Language {
	Italiano,
	English,
	Francais
	}

abstract sig TransportationMean {
	belongsToCompany: lone TransportationCompany
	}

one sig Foot, Bicycle, Car, Taxi, Metro, Tram extends TransportationMean {}

sig Preferences {
	ecoFriendly: Bool,
	disabledTranMean: set TransportationMean
	} 

abstract sig TransportationMeanConstraint {
	associatedToTranMean: TransportationMean
	}

sig DistanceConstraint extends TransportationMeanConstraint { 
	fromValue: Int,
	toValue: Int
	} { fromValue >= 0
		  toValue >= 0
		  fromValue < toValue }

sig TimeWindowConstraint extends TransportationMeanConstraint{
	from: Time,
	to: Time
	} { from.value < to.value }


// === ADDITIONAL SIGNATURES ===
sig SuggestedSolutions {
	suggestTo: User,
	containsSolutions: some Solution
	}

sig Solution {
	suggestTranMean: some TransportationMean,
	forAppointment: Appointment,	
	}


// === FACTS ===
fact EmailsAreUnique {
	all disjoint u1, u2: User | u1.email != u2.email 
	}

fact NoOverlappingLocations {
	all disjoint l1, l2: Location | (l1.latitude != l2.latitude) || (l1.longitude != l2.longitude)
	}

fact TimeIsUnique {
	all disjoint t1, t2: Time | t1.value != t2.value
	}

fact UserIsNotInTwoDifferentLocation {
	all u1, u2: User | u1.currentlyAtLoc = u2.currentlyAtLoc implies u1 != u2
	}

fact ATicketBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.ownsTicket & u2.ownsTicket = none
	}

fact APreferenceBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.hasPreferences & u2.hasPreferences = none
	}

fact TranMeanConstraintsRefersOnlyToOneUser {
	all disjoint u1, u2: User | u1.hasConstraints & u2.hasConstraints = none
	}

fact ABreakWindowIsSetOnlyByOneUser {
	all disjoint u1, u2: User | u1.setBreakWindows & u2.setBreakWindows = none
	}

fact AnAppointmentIsCreatedOnlyByOneUser {
	all disjoint u1, u2: User | u1.createsAppointment & u2.createsAppointment = none
	}

fact ATravelPlanBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.hasTravelPlan & u2.hasTravelPlan = none
	}

fact DisabledTranMeansAreNotSuggested {
	all p: Preferences, s: SuggestedSolutions, u: User |
	p in u.hasPreferences and
	s.suggestTo = u and
	u.hasPreferences.disabledTranMean & (s.containsSolutions).suggestTranMean = none
	}

// if an appointment is associated to a user travel plan, the user must partecipate to the appointment
fact ConsistentUserTravelPlanAppointment { 
	all u: User, a: Appointment, tp: TravelPlan | 
	(tp.forAppointment = a and tp in u.hasTravelPlan) implies (a in u.partecipatesToAppointment)
	}

fact AppointmentCreationImpliesPartecipation {
	all u: User, a: Appointment | 
	(a in u.createsAppointment) implies (a in u.partecipatesToAppointment)
	}
	
pred show {}

run show






