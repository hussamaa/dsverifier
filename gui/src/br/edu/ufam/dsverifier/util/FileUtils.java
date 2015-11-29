package br.edu.ufam.dsverifier.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import br.edu.ufam.dsverifier.domain.SpaceState;

public class FileUtils {

	private static FileUtils instance;

	private FileUtils() {
	}

	public static FileUtils getInstance() {
		if (instance == null) {
			instance = new FileUtils();
		}
		return instance;
	}

	public static void createFile(final String fileName,
			final String strBuilderSpaceState) throws IOException {
		final File file = new File(fileName);
		try (BufferedWriter writer = new BufferedWriter(new FileWriter(file))) {
			writer.write(strBuilderSpaceState);
		}
	}

	public static SpaceState readFile(final String fileName ) {
		final StringBuilder strSpaceStateValues = new StringBuilder();
		final SpaceState spaceStateObject = new SpaceState();
		try {
			final FileReader inputFile = new FileReader(fileName);
			final BufferedReader bufferReader = new BufferedReader(inputFile);
			String line;
			while ((line = bufferReader.readLine()) != null) {
				strSpaceStateValues.append(line + "\n");
			}
			bufferReader.close();
		} catch (final Exception e) {
			System.out.println("Error while reading file line by line:"
					+ e.getMessage());
		}

		SpaceStateUtils.setSpaceStateObject(strSpaceStateValues, spaceStateObject);

		return spaceStateObject;
	}

	public static void deleteFile(final File file) {
		file.delete();
	}

	public static boolean isFileExists(final String fileName) {
		final File f = new File(fileName);
		if (f.exists() && !f.isDirectory()) {
			return true;
		}
		return false;
	}

}
