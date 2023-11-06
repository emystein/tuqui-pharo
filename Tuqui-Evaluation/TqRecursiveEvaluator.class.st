Class {
	#name : #TqRecursiveEvaluator,
	#superclass : #TqEvaluator,
	#category : #'Tuqui-Evaluation-Runtime'
}

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
TqRecursiveEvaluator >> evaluateMethodStatements: aTqMethod [
	| last result printStream |
	last := nil.
	aTqMethod statements do: [ :node |
		last := node.
		"
		printStream := WriteStream on: String new.
		node printOn: printStream.
		printStream nextPut: Character cr.
		Transcript show: printStream contents.
		"
		result := node acceptVisitor: self.
	].

	^ (last notNil and: [ last isReturn ])
		  ifTrue: [ result]
		  ifFalse: [ self context receiver ]

]

{ #category : #'as yet unclassified' }
TqRecursiveEvaluator >> evaluatePrimitive: aTqMethod [ 
	| primitive |
	primitive := self primitiveFor: aTqMethod pragma name.
	^ primitive value.
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
TqRecursiveEvaluator >> lookup: aSymbol startingAt: behavior [
	^ self lookup: aSymbol startingAt: behavior sendSite: nil
]

{ #category : #accessing }
TqRecursiveEvaluator >> lookup: aSymbol startingAt: behavior sendSite: anUndefinedObject [

	behavior isImmediate ifTrue: [ ^ aSymbol ].

	(aSymbol asLocalString beginsWith: '_') ifTrue: [ ^ aSymbol ].

	^ runtime doLookup: aSymbol startingAt: behavior

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
	receiver isBlock ifTrue: [ context beBlock ].
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
TqRecursiveEvaluator >> visitAssignment: aTqAssignment [

	| binding value |
	value := aTqAssignment expression acceptVisitor: self.
	binding := aTqAssignment assignees last binding.
	^ binding assign: value within: context
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitBlock: aTqBlock [
	^ self context captureClosure: aTqBlock

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

	| receiver searchStartingAtSuper behavior arguments method sexpressions |
	
	receiver := aTqMessage receiver acceptVisitor: self.
		
	searchStartingAtSuper := false.
	behavior := searchStartingAtSuper
		            ifTrue: [ runtime superBehaviorOf: context classBinding ]
		            ifFalse: [ runtime behaviorOf: receiver ].

	method := self lookup: aTqMessage selector startingAt: behavior.

	arguments := aTqMessage arguments collect: [ :arg2 | arg2 acceptVisitor: self ].

	(undermessages includesKey: method) ifTrue: [
		^ (undermessages at: method) value: receiver value: arguments ].
	
	self pushFrameFor: method receiver: receiver arguments: arguments.

	sexpressions := runtime sexpressionsOf: method.
	^ self visitMethod: sexpressions
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitMethod: aMethod [
	| result |
	result := aMethod isPrimitive
		  ifTrue: [ self evaluatePrimitive: aMethod ]
		  ifFalse: [ self evaluateMethodStatements: aMethod ].
	self popFrame.
	^ result.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitNonLocalReturn: aTqReturn [
	| value |
	value := aTqReturn expression acceptVisitor: self.
	context homeContext nonLocalReturn: value.
]

{ #category : #visiting }
TqRecursiveEvaluator >> visitReturn: aTqReturn [

	| value returnValue |	
	aTqReturn local ifFalse: [ ^ self visitNonLocalReturn: aTqReturn ].
	value := aTqReturn expression acceptVisitor: self.
	"returnValue := self context return: value."
	"Moved at the end of visitMethod"
	"self popFrame."
	^ value
]
