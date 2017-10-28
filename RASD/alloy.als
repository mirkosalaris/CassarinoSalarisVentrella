// ================================================
// ======================== PRIMITIVE SIGNATURES
sig Name {}

sig Surname {}

sig Email {}

sig Address {}

sig Double {}

enum Bool {
	True,
	False
	}

// ================================================
// ======================== SIGNATURES
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
	participatesToAppointment: set Appointment,
	hasTravelPlan: set TravelPlan,
	currentlyAtLoc: Location
	}

sig Appointment {
	id: Int,
	start: Time,
	end: Time, 
	atLocation: Location,
	hasType: AppointmentType,
	isRepeatable: lone RepeatableAppointment,
	isModified: Bool,
	isIncoming: Bool
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
	startRide: Ride,
	intermediateRides: set Ride,
	endRide: Ride,
	forAppointment: Appointment
	} {
		passengers >= 0
		baggage >= 0

		// structural constraints on start, intermediate and end Rides
		no ir: intermediateRides | startRide = ir or endRide = ir
		lone ir: intermediateRides | startRide.toLocation = ir.fromLocation
		lone ir: intermediateRides | endRide.fromLocation = ir.toLocation
		no ir: intermediateRides | startRide.fromLocation = ir.toLocation
		no ir: intermediateRides | endRide.toLocation = ir.fromLocation
		all ir: intermediateRides | ir.toLocation = endRide.fromLocation or
			one ir1: intermediateRides | ir.toLocation = ir1.fromLocation
		all ir: intermediateRides | ir.fromLocation = startRide.toLocation or
			one ir1: intermediateRides | ir.fromLocation = ir1.toLocation
		#intermediateRides = 0 implies
			(startRide = endRide or startRide.toLocation = endRide.fromLocation)
		}

// retrieves the whole set of Rides of a travel plan
fun travelPlanRides[t: TravelPlan] : some Ride {
	t.startRide + t.intermediateRides + t.endRide
}

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
		  (atLeast.value > 0 and atLeast.value < minus[to.@value, from.@value]) }

enum Language {
	Italiano,
	English,
	Francais
	}

abstract sig TransportationMean {
	belongsToCompany: lone TransportationCompany
	}

one sig Foot, MoBike, PersonalCar, EnjoyCar, Metro, Tram extends TransportationMean {}

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

// ================================================
// ======================== ADDITIONAL SIGNATURES
sig SuggestedSolutions {
	suggestTo: User,
	containsSolutions: some Solution
	}

sig Solution {
	suggestTranMean: some TransportationMean,
	forAppointment: Appointment,	
	}

sig Device {
	belongsTo: User,
	language: Language
}

sig AppInstance{
	installedOn: Device,
	displayLanguage: Language
}{ let d = installedOn |
			( d.language not in SupportedLanguages.setOfLanguages implies ( displayLanguage = English )
			else (displayLanguage = d.language) ) 
			}


one sig SupportedLanguages {
	setOfLanguages: set Language
}

sig Person {
	name: Name,
	surname: Surname,
	email: Email,
	isUser: lone User
}

sig Invitation {
	fromUser: User,
	toEmail: Email,
	forAppointment: Appointment
}{
	forAppointment in fromUser.createsAppointment
	fromUser.email != toEmail
}

sig Notification {
	toUser: User,
	incomingAppointment: Appointment
}

// ================================================
// ======================== FACTS
fact EmailsAreUnique {
	all disjoint u1, u2: User | u1.email != u2.email 
	}

fact NoOverlappingLocations {
	all disjoint l1, l2: Location | (l1.latitude != l2.latitude) || (l1.longitude != l2.longitude)
	}

fact TimeIsUnique {
	all disjoint t1, t2: Time | t1.value != t2.value
	}

fact ATicketBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.ownsTicket & u2.ownsTicket = none
	}

fact TicketMustBeAssociatedToRides {
	all t: Ticket | some r: Ride | t in r.makeUseTicket
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

fact AppointmentsMustBeCreatedOnlyByUsers {
	all a: Appointment | some u: User | a in u.createsAppointment
	}

fact ATravelPlanBelongsOnlyToOneUser {
	all disjoint u1, u2: User | u1.hasTravelPlan & u2.hasTravelPlan = none
	}

// if a User has disabled a transportation mean, it should never be suggested to him/her
fact DisabledTranMeansAreNotSuggested {
	all p: Preferences, s: SuggestedSolutions, u: User |
	p in u.hasPreferences and
	s.suggestTo = u and
	u.hasPreferences.disabledTranMean & (s.containsSolutions).suggestTranMean = none
	}

// if an appointment is associated to a travel plan of a User, the User must participate to the appointment
fact ConsistentUserTravelPlanAppointment { 
	all u: User, a: Appointment, tp: TravelPlan | 
	(tp.forAppointment = a and tp in u.hasTravelPlan) implies (a in u.participatesToAppointment)
	}

fact AppointmentCreationImpliesParticipation {
	all u: User, a: Appointment | 
	(a in u.createsAppointment) implies (a in u.participatesToAppointment)
	}

// there is not the possibility to have a name, surname, email, address, appointment
//  type or transportation company without associations with something
fact AllNameMustBelongToUsers {
	all n: Name | some u: User | u.name = n
	}

fact AllSurnameMustBelongToUsers {
	all s: Surname | some u: User | u.surname = s
	}

fact AllEmailMustBelongToPersonos {
	all e: Email | some p: Person | p.email = e
	}

fact AllAddressesMustBelongToLocations {
	all a: Address | some loc: Location | loc.address = a
	}

fact TicketMustBelongToUsers {
	all t: Ticket | some u: User | t in u.ownsTicket
	}

fact AllTicketsMustBeProvidedByTranCompany {
	all t: Ticket | some tc: TransportationCompany | t.providedByCompany = tc
}

fact TranCompanyMustBeAssociatedWithTranMean {
	all tc: TransportationCompany | some tm: TransportationMean | tm.belongsToCompany = tc
	}

// No tickets for personal and shared transportation means
fact TicketsUsedOnlyIfNecessary {
	all t: Ticket | (Foot & t.usedFor = none) and
	(MoBike & t.usedFor = none) and 
	(PersonalCar & t.usedFor = none) and
	(EnjoyCar & t.usedFor = none)
	}

fact NoTranCompanyForPersonalTranMeans  {
	(Foot.belongsToCompany = none) and
	(PersonalCar.belongsToCompany= none)
	}

fact TranMeanConstraintsMustBelongToUsers {
	all tmc: TransportationMeanConstraint | some u: User | tmc in u.hasConstraints 
	}

fact BreakWindowMustBeSetByUsers {
	all bw: BreakWindow | some u: User | bw in u.setBreakWindows
	}

fact RideMustBelongToTravelPlans {
	all r: Ride | some tp: TravelPlan | r in travelPlanRides[tp]
	}

fact RideBelongsToOnlyOneTravelPlan {
	all disjoint tp1, tp2: TravelPlan | travelPlanRides[tp1] & travelPlanRides[tp2] = none
}

fact TravelPlanMustBelongToUsers {
	all tp: TravelPlan | some u: User | tp in u.hasTravelPlan
	}

fact SolutionMustBeSuggested {
	all s: Solution | some ss: SuggestedSolutions | s in ss.containsSolutions
	}

fact LocationAssociatedToRideAppointmentOrUser {
	all l: Location | some r: Ride, a: Appointment, u: User |
	l in (r.fromLocation + r.toLocation + a.atLocation + u.currentlyAtLoc)
	}

fact RepeatableAppointmentIsAnAppointment {
	all ra: RepeatableAppointment | some a: Appointment | ra in a.isRepeatable
	}

fact RepeatableAppointmentsAtTheSameTime {
	all a1, a2: Appointment | (a1.isRepeatable = a2.isRepeatable) implies  
	(a1.start = a2.start and a1.end = a2.end)
	}

fact NoStartRideFromAppointmentLocation {
	all tp: TravelPlan | tp.startRide.fromLocation != tp.forAppointment.atLocation
}

fact SameEmailImpliesSamePerson {
	all p1, p2: Person | p1.email = p2.email implies (samePerson[p1, p2])
}

fact SamePersonImpliesOldAndNew {
	 all disjoint p1, p2: Person | samePerson[p1, p2] implies
		((p1.isUser = none and p2.isUser != none) or (p1.isUser != none and p2.isUser = none))
}

fact UserAndPersonSameData {
	all p: Person | p.isUser != none implies
		let u = p.isUser |
		p.email = u.email and
		p.name = u.name and
		p.surname = u.surname
}

fact EveryUserHasA2Person {
	all u: User | some disjoint p1, p2: Person | p1.isUser = u and samePerson[p1, p2]
}

fact IsModifiedImpliesAnotherAppointment {
	all apOld: Appointment | some apNew: Appointment |
		apOld.isModified = True implies
		apOld.id = apNew.id and apOld != apNew and apNew.isModified = False
}

fact SameAppointmentIdSameUser {
	all disjoint ap1, ap2: Appointment | all u: User |
		ap1.id = ap2.id and
		(ap1 in u.participatesToAppointment implies (ap2 in u.participatesToAppointment))
		and
		(ap1 in u.createsAppointment implies (ap2 in u.createsAppointment))
}

fact AllUsersMustBeCreatorOrInvited {
	all a: Appointment, u: User | a in u.participatesToAppointment implies 
	(a in u.createsAppointment or invitedToAppointment[u, a])
}

fact NotificationOnlyIfAppointmentIsIncoming {
	all n: Notification | n.incomingAppointment.isIncoming = True
}

fact NotificationForAllIncomingAppointment {
	all a: Appointment, u: User |
	(a.isIncoming = True and a in u.participatesToAppointment)
	implies
	(one n1: Notification | n1.incomingAppointment = a and n1.toUser = u)
}

fact UserReceivesNotificationOfOwnedAppointments {
	all n: Notification, u: User |
		n.toUser = u implies n.incomingAppointment in u.participatesToAppointment
}

fact EachDeviceHasMaxOneAppInstance {
	all d: Device | lone a: AppInstance | a.installedOn = d
}

fact EveryUserHasAtLeastOneAppInstance {
	all u: User | some a: AppInstance | a.installedOn.belongsTo = u
}

fact TravelPlanAppointmentLocationConsistency {
	all tp: TravelPlan, ap:Appointment  | ap=tp.forAppointment implies (ap.atLocation=tp.endRide.toLocation)
 }

fact OneConstraintperTravelMean {
	all u:User, tc1, tc2:TransportationMeanConstraint | ( tc1  in u.hasConstraints and tc2 in u.hasConstraints
	and  tc1.associatedToTranMean = tc2.associatedToTranMean ) implies (tc1 = tc2)
} 

fact TicketWithOneUser{
	all t:Ticket | one u:User | t in u.ownsTicket
}

fact TicketWithAtLeastOneRide{
	all t:Ticket | some r:Ride | r.makeUseTicket = t
}

fact TicketConsistency{
	all t:Ticket, r:Ride, u:User, tp:TravelPlan | ( r in (tp.startRide + tp.intermediateRides + tp.endRide) 
	and tp in u.hasTravelPlan and r.makeUseTicket = t ) implies t in u.ownsTicket
}



// ================================================
//  ======================== UTILITY PREDICATES
pred samePerson[p1, p2: Person] {
	p1.email = p2.email and p1.name=p2.name and p1.surname = p2.surname
}

pred invitedToAppointment[u: User, a: Appointment] {
	some i: Invitation | i.forAppointment = a and i.toEmail = u.email
}

// ================================================
// ======================== ASSERTIONS
assert CanDisplayInAllSupportedLanguages {
	no l: AppInstance.installedOn.language |
		l in SupportedLanguages.setOfLanguages and
		no ap: AppInstance | ap.displayLanguage = l
}
check CanDisplayInAllSupportedLanguages

assert EveryPersonShouldBeAbleToHaveAnAccount {
	#User > 0
	implies
	some p1, p2: Person, u: User | 
		p1.email = p2.email and p1.isUser = none and p2.isUser = u
}
check EveryPersonShouldBeAbleToHaveAnAccount

assert UserAlwaysNotified {
	all a: Appointment, u: User |
		(a.isIncoming = True and a in u.participatesToAppointment)
		implies
		(one n: Notification | n.toUser = u and n.incomingAppointment = a)
}
check UserAlwaysNotified for 2

// ================================================
// ======================== RUNNABLE PREDICATES

pred showSomeAppointmentModified {
	some ap: Appointment | ap.isModified = True
}
run showSomeAppointmentModified

pred showSomeMeeting {
	some a: Appointment, disjoint u1, u2: User |
		 a in u1.participatesToAppointment and a in u2.participatesToAppointment
}
run showSomeMeeting for 4

pred show {
	#Appointment = 2 and
	#User = 1 and
	#Notification > 0 and
	#TravelPlan > 1 and
	#Solution > 1 and
	#SupportedLanguages.setOfLanguages > 1
}

run show for 5 but 4 Notification, 8 Int
