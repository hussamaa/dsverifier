/*******************************************************************\

Module: Print standard messaged about DSVerifier

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#ifndef UTILS_PRINT_MESSAGES_H
#define UTILS_PRINT_MESSAGES_H

void show_underflow_message()
{
  std::cout <<
    "UNDERFLOW detected: An fixed-point arithmetic underflow occurs after delta transformation"
	<< std::endl;
}

void show_delta_not_representable()
{
  std::cout <<
    "DsVerifier is unable to represent this value in delta-form using this precision"
	<< std::endl;
}

void show_verification_error()
{
  std::cout << std::endl << "VERIFICATION ERROR" << std::endl;
}


void show_verification_successful()
{
  std::cout << std::endl << "VERIFICATION SUCCESSFUL" << std::endl;
}


void show_verification_failed()
{
  std::cout << std::endl << "VERIFICATION FAILED" << std::endl;
}

#endif // UTILS_PRINT_MESSAGES_H
