/*******************************************************************
 Function: print_counterexample_data_for_restricted_properties

 Inputs:

 Outputs:

 Purpose: print counterexample data for overflow/stability/minimum phase properties

 \*******************************************************************/

void print_counterexample_data_for_restricted_properties()
{
	try
	{
		std::cout << std::endl << "Counterexample Data:" << std::endl;

		bool is_delta_realization = (desired_realization == "DDFI"
				|| desired_realization == "DDFII" || desired_realization == "TDDFII");

		std::cout << "  Property = " << desired_property << std::endl;
		cplus_print_array_elements_ignoring_empty("  Numerator ", ds.b, ds.b_size);
		cplus_print_array_elements_ignoring_empty("  Denominator ", ds.a,
				ds.a_size);
		std::cout << "  Numerator Size = " << ds.b_size << std::endl;
		std::cout << "  Denominator Size = " << ds.a_size << std::endl;

		if (is_delta_realization)
			std::cout << "  Delta: " << impl.delta << std::endl;

		std::cout << "  X Size = " << desired_x_size << std::endl;
		std::cout << "  Sample Time = " << ds.sample_time << std::endl;
		std::cout << "  Implementation = " << "<" << impl.int_bits << ","
				<< impl.frac_bits << ">" << std::endl;
		std::cout << "  Realization = " << desired_realization << std::endl;
		std::cout << "  Dynamic Range = " << "{" << impl.min << "," << impl.max
				<< "}" << std::endl;

	} catch (std::regex_error& e)
	{
		std::cout
				<< "[ERROR] It was not able to process the counterexample data. :("
				<< std::endl;
		exit(1);
	}
}

