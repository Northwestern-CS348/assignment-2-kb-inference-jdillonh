import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument
        Args:
            fact (Fact): Fact we're searching for
        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument
        Args:
            rule (Rule): Rule we're searching for
        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB
        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)
        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB
        Args:
            fact (Fact) - Fact to be retracted
        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here

        if not isinstance(fact, Fact):
            print("tried to retract a non-fact")
            if isinstance(fact, Rule):
                print("this is a rule, forget about it!")
                return #piazza says this is right

        #Therefore, when you retract a fact, it would be both supported and
        #asserted.
        #When that happen, you toggle the "asserted" flag and leave it be.
        #  - Zaohao She
        if (len(fact.supported_by) > 1
            and fact.asserted):
            fact.asserted = False
            return
        #If it's not asserted but supported, you do nothing.
        if not fact.asserted and len(fact.supported_by) >= 1:
            return
        #If it's only asserted, you
        #remove its support from all rules / facts involved,
        #and recursively remove those fact / rule that are not asserted
        #and no longer contains any valid support, and remove the
        #fact from the KB itself.
        def recRem(fact, kb): #really fact OR RULE
            """[helper] 
            recursively remove fact, and remove 
            all facts/rules that are no longer supported
            """
            for f in fact.supports_facts:
                f.supported_by = (
                    [t for t in f.supported_by if fact not in t])
                if not f.asserted and len(f.supported_by) == 0:
                    recRem(f, kb)

            for r in fact.supports_rules:
                r.supported_by = (
                    [t for t in r.supported_by if fact not in t])
                if not r.asserted and len(r.supported_by) == 0:
                    recRem(r, kb)

            #remove fact from kb
            try:
                if isinstance(fact, Fact):
                    kb.facts.remove(fact)
            except:
                print("removed a fact that wasn't in the kb")
            try:
                if isinstance(fact, Rule):
                    kb.rules.remove(fact) 
            except:
                print("removed a rule that wasn't in the kb")

        if len(fact.supported_by) == 0:
            recRem(fact, self)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules
        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase
        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
               [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        assert((not isinstance(fact, Fact) and not isinstance(rule, Rule)),
               "not a fact or rule! Bad arguments.")
        assert(len(rule.lhs) > 0,
               "No LHS on this Rule!!")

        binds = match(fact.statement, rule.lhs[0])
        if not binds: return #nothing we can synthesize
        newRHS = instantiate(rule.rhs, binds)

        if len(rule.lhs) == 1:
            newFact = Fact(newRHS, [rule, fact])
            fact.supports_facts += [newFact]
            rule.supports_facts += [newFact]
            kb.kb_add(newFact)
            #assert(len(newFact.supported_by) == 2)
            
        elif len(rule.lhs) > 1:
            newLHS = [instantiate(st, binds)
                      for st in rule.lhs[1:]]
            newRule = Rule([newLHS, newRHS],[(fact, rule)])
            fact.supports_rules += [newRule]
            rule.supports_rules += [newRule]
            kb.kb_add(newRule)
            #assert(len(newRule.supported_by) == 2)

            
#"""
#
#INFER :
#make sure bindings are niether False, nor Empty 
#(if Rule and Fact are == then they will have empty bindings)
#
#if the LHS is only 1 thing, then when ou have a fact that matched that you can infer the RHS of a new Fact.
#(several LHS's and ANDED)
#
#if the first LHS matches, and there are more LHS's 
#
#if len(LHS) == 1:
#   # try to make a fact
#if len(LHS) > 1: #already know that: and there are bindings on LHS[0]:
#   # make a RUule, we don't have enough infor to make a Fact
#
#
#"""
