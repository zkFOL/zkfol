Class {
	#name : 'ZkfolQuery',
	#superclass : 'BeamProxyObject',
	#instVars : [
		'announcer'
	],
	#category : 'Zkfol-Proxies',
	#package : 'Zkfol',
	#tag : 'Proxies'
}

{ #category : 'accessing' }
ZkfolQuery class >> elixirClass [
	"The proxy factory dispatches me for the query handle."
	^ 'Zkfol.Query'
]

{ #category : 'accessing' }
ZkfolQuery >> announcer [
	"Answer arrivals, for the view to follow."
	^ announcer ifNil: [ announcer := Announcer new ]
]

{ #category : 'stepping' }
ZkfolQuery >> close [
	"Discard the query's branch and stop its process; idempotent."
	^ self evaluateOrNil: 'Zkfol.Query.close(' , self resolve , ')'
]

{ #category : 'stepping' }
ZkfolQuery >> findall [
	"Every remaining answer, up to a sanity bound: a relation can be
	 infinite, a button should not be."
	256 timesRepeat: [ (self next isKindOf: Collection) ifFalse: [ ^ self ] ]
]

{ #category : 'views' }
ZkfolQuery >> gtAnswersFor: aView [
	"The answers the node has handed out. Plus is the semicolon, one
	 more answer; play takes the rest boundedly; and a click opens the
	 answer as the statement it satisfies."
	<gtView>
	<gtBeamView>
	^ aView columnedList
		title: 'Answers';
		priority: 1;
		items: [ self taken ];
		column: '#' text: [ :each :i | i printString ] width: 40;
		column: 'Answer' text: [ :each | each printString ];
		send: [ :each | self statementAt: (self taken indexOf: each) ];
		actionButtonIcon: BrGlamorousVectorIcons add
			tooltip: 'Next (;)'
			action: [ :aButton :aTab | self next ];
		actionButtonIcon: BrGlamorousVectorIcons play
			tooltip: 'Find all (bounded)'
			action: [ :aButton :aTab | self findall ];
		updateWhen: Announcement in: self announcer
]

{ #category : 'views' }
ZkfolQuery >> gtProgramFor: aView [
	"The AL program my query executes on its branch; AL draws it."
	<gtView>
	<gtBeamView>
	| program |
	program := self evaluateOrNil: self resolve , '.program'.
	(program isKindOf: ALObject) ifFalse: [ ^ aView empty ].
	^ aView forward
		title: 'Program';
		priority: 9;
		object: [ program ];
		view: #gtMethodsFor:
]

{ #category : 'stepping' }
ZkfolQuery >> next [
	"One more answer off the node; nil when the search is exhausted, a
	 refusal when the node refuses."
	| said |
	said := self plainFetch: 'Zkfol.Query.next(' , self resolve , ')'.
	self announcer announce: Announcement new.
	(said isKindOf: ZkfolRefusal) ifTrue: [ ^ said ].
	said = #exhausted ifTrue: [ ^ nil ].
	(said isKindOf: Collection) ifFalse: [ ^ nil ].
	said first = #ok ifTrue: [ ^ said second ].
	^ ZkfolRefusal because: said printString
]

{ #category : 'stepping' }
ZkfolQuery >> statementAt: aOneBasedIndex [
	"Answer k as the statement it satisfies, bridged and provable."
	^ self evaluateOrNil:
		'Zkfol.Query.statement(' , self resolve , ', ' , aOneBasedIndex printString , ')'
]

{ #category : 'accessing' }
ZkfolQuery >> taken [
	"Every answer the node has handed out, oldest first."
	| said |
	said := self plainFetch: 'Zkfol.Query.taken(' , self resolve , ')'.
	^ (said isKindOf: ZkfolRefusal) ifTrue: [ #() ] ifFalse: [ said ]
]
