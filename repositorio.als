-----------------------------------------------------------------------------------------------------------
--| Alloy Project - Computação@UFCG
--|
--| Group 11 : Git Repository
--|
--| Diego Ribeiro de Almeida
--| Iago Tito Oliveira
--| Paulo Mateus Alves Moreira
--| Raiany Rufino Costa da Paz
--|
--| Client: Jose Ivan
--| Professor: Tiago Massoni
-----------------------------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------------------------
--> Signatures
-----------------------------------------------------------------------------------------------------------
module GitRepository

one sig Repository {
	clients: set Client
}

sig Client {
	projectPastes: set ProjectPaste
}

// Pastes
abstract sig Paste {}

sig ProjectPaste extends Paste {
	alfa: one AlfaVersion ,
	beta: lone BetaVersion ,
	version: set Version ,
	archives: one Archives
}

abstract sig VersionPaste extends Paste {
	code: one Code ,
	test: one Test ,
	tecnologies: one Tecnologies ,
	language: one Language ,
	requirimentsMet: one RequirementsMet
}

// In ProjectPaste

sig Archives {
	projectID: one ProjectID ,
	members: one Member ,
	functionalRequiriments: one FunctionalRequirements ,
	nonFunctionalRequiriments: one NonFunctionalRequirements ,
	period: one Period
}

// Inside Archives have:

sig ProjectID {}

sig Member {}

abstract sig Requirements {}

sig FunctionalRequirements extends Requirements {}

sig NonFunctionalRequirements extends Requirements {}

sig Period {
	begin: one Begin ,
	end: lone End ,
	inProgress: lone InProgress
}

sig Begin {}

sig End {}

sig InProgress {}

// Inside VersionPaste have:

sig Code {}

sig Test {}

sig Tecnologies {}

sig Language {}

sig RequirementsMet {}


// We used just 3 possible versions because the program can't run more than this, but that show's the ideia

sig AlfaVersion extends VersionPaste {}

sig BetaVersion extends VersionPaste {}

sig Version extends VersionPaste {}

-----------------------------------------------------------------------------------------------------------
--> Facts
-----------------------------------------------------------------------------------------------------------

fact Repository {
	// The Repository have at least one Client
	one r: Repository | some r.clients
}

fact Client {
	// All Clients must be in the Repository
	all c: Client | some clients.c

	// All Clients have at least one Project Paste
	all c: Client | some c.projectPastes
}

fact ProjectPastes {
	// Each Project Paste is in only one Client
	all pp: ProjectPaste | one projectPastes.pp

	// All Project Paste have at least one Version Paste
	all pp: ProjectPaste | one pp.alfa

	// If the value of Version is 0 or the value of Beta is 0, it means that Version cannot exist 
	// (you can't have a Version without a BetaVersion before
	all pp: ProjectPaste | ! haveVersion[pp] => no pp.version
}

fact VersionPastes {
	// Each Version Pastes is in only one Project Paste
	all a: AlfaVersion | one alfa.a
	all b: BetaVersion | one beta.b
	all o: Version | one version.o
}

fact Archives {
	// Each Archive is in only one Project Paste
	all a: Archives | one archives.a
}

fact ProjectID {
	// Each ProjectID is in only one Archive
	all id: ProjectID | one projectID.id
}

fact Member {
	// Each Member is in only one Archive
	all m: Member | one members.m
}

fact FunctionalRequirements {
	// Each Functional Requirements is in only one Archive
	all fr: FunctionalRequirements | one functionalRequiriments.fr
}

fact NonFunctionalRequirements {
	// Each Non Functional Requirements is in only one Archive
	all nfr: NonFunctionalRequirements | one nonFunctionalRequiriments.nfr
}

fact Period {
	// Each Period is in only one Archive
	all p: Period | one period.p

	// Each Begin is in only one Period
	all b: Begin | one begin.b

	// Each End is in only one Period
	all e: End | one end.e

	// Each InProgress is in only one Period
	all p: InProgress | one inProgress.p
	
	// If the Project ended, it is not In Progress
	all p: Period | ended[p] => no p.inProgress

	// If the Project does not ended, it is In Progress
	all p: Period | ! (ended[p]) => one p.inProgress
}

fact Code {
	// Each Code is in only one Version Paste
	all c: Code | one code.c
}

fact Test {
	// Each Test is in only one Version Paste
	all t: Test | one test.t
}

fact Tecnologies {
	// Each Tecnologies is in only one Version Paste
	all tec: Tecnologies | one tecnologies.tec
}

fact Language {
	// Each Language is in only one Version Paste
	all l: Language | one language.l
}

fact RequirimentsMet {
	// Each Requiriments Met is in only one Version Paste
	all r: RequirementsMet | one requirimentsMet.r
}
-----------------------------------------------------------------------------------------------------------
--> Predicates
-----------------------------------------------------------------------------------------------------------

// If the project is ended, return True
pred ended [p:Period] {
	# p.end = 1
}

pred haveBeta [pp:ProjectPaste] {
	# pp.beta = 1
}

pred haveVersion[pp:ProjectPaste] {
	# pp.version = 1 and haveBeta[pp]
}


-----------------------------------------------------------------------------------------------------------
--> Asserts
-----------------------------------------------------------------------------------------------------------

assert Repository {
	all r: Repository | # r.clients > 0
}

assert Clients {
	all c: Client | # c.projectPastes > 0
}

assert ProjectPastes {
	all pp: ProjectPaste | # pp.alfa = 1
	all pp: ProjectPaste | # pp.beta = 0 or # pp.beta = 1

	all pp: ProjectPaste | # pp.version > 0 => # pp.beta = 1
}

assert  Period {
	all p: Period | # p.begin = 1
	all p: Period | # p.end + # p.inProgress = 1
} 


// check Repository for 20
// check Clients for 20
// check ProjectPastes for 20
// check Period for 20




pred show[] {}
run show for 10
