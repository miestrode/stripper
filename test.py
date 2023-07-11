from pddl import formatter
from pddl.parser.domain import DomainParser

import core

with open("domain.pddl") as file:
    contents = file.read()

    parser = DomainParser()

    domain = parser(contents)

    core.make_domain_mutatable(domain)
    core.remove_domain_equality_requirement(domain)
    core.remove_domain_typing_requirement(domain)

    negative_precondition_map = core.remove_domain_negative_preconditions_requirement(domain)

    print(formatter.domain_to_string(domain))
    print(negative_precondition_map)
