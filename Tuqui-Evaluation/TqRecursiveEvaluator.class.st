Class {
	#name : #TqRecursiveEvaluator,
	#superclass : #TqEvaluator,
	#category : #'Tuqui-Evaluation-Runtime'
}

{ #category : #visiting }
TqRecursiveEvaluator >> evalMethodStatements: aTqMethod [
	| last result |
	last := nil.
	aTqMethod statements do: [ :node |
		last := node.
		result := node acceptVisitor: self.
	].
	^ (last notNil and: [ result notNil ])
		  ifTrue: [ result]
		  ifFalse: [ self context receiver ]

]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateClosure: receiver whileFalse: arg [
	| result |
	[ result := self evaluateClosure: receiver.
	self booleanFrom: result ]
		whileFalse: [ self evaluateClosure: arg ].
	^ receiver
]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateClosure: receiver whileTrue: arg [
	| result |
	[ result := self evaluateClosure: receiver.
	self booleanFrom: result ] whileTrue: [ self evaluateClosure: arg ].
	^ receiver
]

{ #category : #private }
TqRecursiveEvaluator >> evaluateClosure: closure withArgs: arguments [
	| block sblock receiver result |
	block := runtime closureBlock: closure.
	sblock := runtime blockExecutableCode: block.
	receiver := (runtime blockCapturesSelf: block)
		            ifTrue: [ closure at: 1 ]
		            ifFalse: [ nilObj ].
	context := TqRecursiveLinkedContext new
		runtime: runtime;
		beBlock;
		parent: context;
		self: receiver;
		initializeForBlock: sblock args: arguments closure: closure.
	result := nilObj.
	sblock statements do: [ :node | result := node acceptVisitor: self ].
	^ result
]

{ #category : #visiting }
TqRecursiveEvaluator >> evaluateSend: symbol to: receiver with: anArray [

	^self
		       send: symbol
		       to: receiver
		       with: anArray
		       super: false
]

{ #category : #visiting }
TqRecursiveEvaluator >> hasFinished [
	^context isNil
]

{ #category : #visiting }
TqRecursiveEvaluator >> initializePrimitives [ 
	super initializePrimitives.
	primitives 
		at: #ClosureWhileTrue put: self primitiveClosureWhileTrue;
		at: #ClosureWhileFalse put: self primitiveClosureWhileFalse
]

{ #category : #accessing }
TqRecursiveEvaluator >> lookup: aSymbol startingAt: behavior sendSite: anUndefinedObject [

	| methodDictionary |
	behavior isImmediate ifTrue: [ ^ aSymbol ].

	(aSymbol asLocalString beginsWith: '_') ifTrue: [ ^ aSymbol ].

	methodDictionary := behavior slots
		                    ifEmpty: [ behavior behavior slots at: 2 ]
		                    ifNotEmpty: [ behavior slots at: 2 ].

	^ methodDictionary atKey: aSymbol ifAbsent: [ nil ]
]

{ #category : #'as yet unclassified' }
TqRecursiveEvaluator >> popFrame [
	context := context parent
]

{ #category : #visiting }
TqRecursiveEvaluator >> primitiveClosureWhileFalse [
	^ [ self
		evaluateClosure: context self
		whileFalse: context arguments first ]
]

{ #category : #visiting }
TqRecursiveEvaluator >> primitiveClosureWhileTrue [
	^ [ self
		evaluateClosure: context self
		whileTrue: context arguments first ]
]

{ #category : #'as yet unclassified' }
TqRecursiveEvaluator >> pushFrameFor: method receiver: receiver arguments: arguments [ 
	| size environment |
	size := runtime methodEnvironmentSize: method.
	environment := runtime newEnvironmentSized: size.
	context := TqRecursiveLinkedContext new
		           runtime: runtime;
		           self: receiver;
		           arguments: arguments;
		           environment: environment;
		           parent: context;
		           method: method.
]

{ #category : #controlling }
TqRecursiveEvaluator >> send: aSymbol to: receiver with: arguments super: aBoolean [ 
	^  self send: aSymbol to: receiver with: arguments super: aBoolean sendSite: nil
]

{ #category : #visiting }
TqRecursiveEvaluator >> send: aSymbol to: receiver with: arguments super: aBoolean sendSite: anSMessage [

	| behavior method environment size |
	
	aSymbol asLocalString = 'yourself' ifTrue: [ ^ receiver ].
	
	behavior := aBoolean
		            ifTrue: [ runtime superBehaviorOf: context classBinding ]
		            ifFalse: [ runtime behaviorOf: receiver ].
	method := self
		          lookup: aSymbol
		          startingAt: behavior
		          sendSite: anSMessage.
	method isBlock ifTrue: [ ^ method value: receiver value: arguments ].
	self ASSERT: method notNil.
	size := runtime methodEnvironmentSize: method.
	environment := runtime newEnvironmentSized: size.
	context := TqRecursiveLinkedContext new
		           runtime: runtime;
		           self: receiver;
		           arguments: arguments;
		           environment: environment;
		           parent: context;
		           method: method.
	^ context evaluateFor: self
]

{ #category : #visiting }
TqRecursiveEvaluator >> superBehaviorOf: class [

	| superclass |
	superclass := self speciesSuperclass: class.
	^ self speciesInstanceBehavior: superclass
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitBlock: aTqBlock [
	^ aTqBlock compiledCode
			ifNil: [ aTqBlock ] 
			ifNotNil: [ self context captureClosure: aTqBlock ]

]

{ #category : #visiting }
TqRecursiveEvaluator >> visitIdentifier: aTqIdentifier [ 
	^ aTqIdentifier binding valueWithin: self context
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitLiteral: aTqLiteral [ 
	^ aTqLiteral value
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitMessage: aTqMessage [

	| receiver receiverIsSuper behavior args method sexpressions |
	
	receiver := aTqMessage receiver acceptVisitor: self.
	
	"TODO: Implement super".
	receiverIsSuper := false.
	behavior := receiverIsSuper
		            ifTrue: [ runtime superBehaviorOf: context classBinding ]
		            ifFalse: [ runtime behaviorOf: receiver ].
	method := self lookup: aTqMessage selector startingAt: behavior sendSite: nil.
	args := aTqMessage arguments collect: [ :arg2 | arg2 acceptVisitor: self ].
	
	(undermessages includesKey: method) ifTrue: [
		^ (undermessages at: method) value: receiver value: args ].

	"method isBlock ifTrue: [ ^ method value: receiver value: args ]."


	" This did the trick for passing tests 110, 111 and 112 the first time (currently replaced with method ifNil: [ ^ receiver ]"		
	"method isBytes ifTrue: [ ^ receiver ]."
	
	method
		ifNil: [ ^ receiver ]
		ifNotNil: [ self pushFrameFor: method receiver: receiver arguments: args].

	sexpressions := runtime sexpressionsOf: method.
	^ self visitMethod: sexpressions.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitMethod: aMethod [
	^ aMethod isPrimitive
		  ifTrue: [ self evalPrimitive: aMethod ]
		  ifFalse: [ self evalMethodStatements: aMethod ]
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitReturn: aTqReturn [

	| value valueToReturn |
	"aTqReturn local ifFalse: [ ^ self visitNonLocalReturn: aTqReturn ]."
	value := aTqReturn expression acceptVisitor: self.
	valueToReturn := self context return: value.
	self popFrame.
	^ valueToReturn
]
