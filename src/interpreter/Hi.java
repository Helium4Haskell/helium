import java.io.*;
import java.awt.*;
import java.awt.image.*;
import java.awt.event.*;

class Hi extends Frame
{
	TextArea outputArea;
	Label   statusLabel;
	TextField inputField;
	Button interruptButton;

	Process process;
	boolean done;

	Hi()
	{
		super("hi");
		setSize(800, 600);

		inputField = new TextField(60);
		inputField.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent ae) {
				handleUserInput(inputField.getText());
			}});

		interruptButton = new Button("Interrupt");
		interruptButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent ae) {
				interruptButton.setEnabled(false);
				statusLabel.setText("Interrupted by user (please wait)");
				process.destroy();
				while (!done)
					try { Thread.sleep(100); } catch (InterruptedException ie) {}
				statusLabel.setText("Done");
			}});

	 LogoCanvas logoCanvas = new LogoCanvas();

		Panel inputAndInterrupt = new Panel();
		inputAndInterrupt.setLayout(new FlowLayout());
		inputAndInterrupt.add(inputField);
		inputAndInterrupt.add(interruptButton);
		inputAndInterrupt.add(logoCanvas);

		outputArea = new TextArea(25, 80);
		outputArea.setFont(new Font("Monospaced", Font.PLAIN, 12));
		outputArea.setEditable(false);

		statusLabel = new Label();

		setLayout(new BorderLayout());
		add(inputAndInterrupt, BorderLayout.NORTH);
		add(outputArea, BorderLayout.CENTER);
		add(statusLabel, BorderLayout.SOUTH);

		addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent we) {
				System.exit(0);
			}});

		setExecuting(false);
		setVisible(true);
	}

	public static void main(String args[])
	{
		try
		{
			new Hi();
		} catch (Exception e)
		{
			System.out.println("Uncaught exception: " + e);
			e.printStackTrace();
			System.exit(0);
		}
	}

	private final static String HI_TEMP_MODULE = "HiTemp";
	private final static String MAIN_FUNCTION = "interpreter_main";
	private final static int OUTPUT_WIDTH = 80;

	void handleUserInput(String input)
	{
		String hiTempFile = HI_TEMP_MODULE + ".hs";

		outputArea.append(">>> " + input + "\n");

		statusLabel.setText("Creating temporary file");

		try
		{
			PrintWriter printWriter =
				new PrintWriter(new FileWriter(hiTempFile), true);
			printWriter.println("module " + HI_TEMP_MODULE + " where");
			printWriter.println(MAIN_FUNCTION + " = " + input);
			printWriter.close();
		} catch (IOException e)
		{
			statusLabel.setText("Failed to write to " + hiTempFile);
			return;
		}

		statusLabel.setText("Running Helium compiler");

		RunProgramResult result;
		try
		{
			result = runProgram("helium " + hiTempFile, null);
		} catch (IOException e)
		{
			statusLabel.setText("Failed to run Helium compiler");
			return;
		}

		outputArea.append(result.output + "\n");

		if (result.exitValue != 0)
			return;

		statusLabel.setText("Running generated code");
		setExecuting(true);
		Thread thread = new Thread(new Runnable() {
			public void run() {
				try
				{
					runProgram("lvmrun " + HI_TEMP_MODULE + ".lvm", outputArea);
				} catch (IOException e)
				{
					statusLabel.setText("Failed to run generated code");
				}
				outputArea.append("\n");
				setExecuting(false);
			}});
		thread.start();
	}

	void setExecuting(boolean executing)
	{
		interruptButton.setEnabled(executing);
		inputField.setEditable(!executing);
		done = !executing;
	}

	RunProgramResult runProgram(String command, TextArea outputArea)
		throws IOException
	{
		StringBuffer outputString = new StringBuffer();
		Runtime runtime = Runtime.getRuntime();

		process = runtime.exec(command);
		BufferedInputStream bis =
			new BufferedInputStream(process.getInputStream());
		int ch, count = 0;
		while ((ch = bis.read()) != -1)
		{
			if (outputArea != null)
			{
				outputArea.append("" + (char) ch);
				count++;
				if (count % OUTPUT_WIDTH == 0) outputArea.append("\n");
			}
			else
				outputString.append((char) ch);
		}
		try
		{
			process.waitFor();
		} catch (InterruptedException ie)
		{
			statusLabel.setText("Waiting for command \"" + command + "\" was interrupted");
			System.exit(0);
		}

		return new RunProgramResult(process.exitValue(), outputString.toString());
	}

}

class RunProgramResult
{
	int exitValue;
	String output;
	RunProgramResult(int exitValue, String output)
	{
		this.exitValue = exitValue;
		this.output = output;
	}
}

class LogoCanvas extends Canvas
{
	 Image logoImage;

		LogoCanvas()
		{
			setSize(150, 45);
			logoImage = Toolkit.getDefaultToolkit().getImage("HeliumLogo.jpg");
			MediaTracker tracker = new MediaTracker(this);
			tracker.addImage(logoImage, 0);
			try {
				tracker.waitForAll();
			} catch (Exception e) {
				System.exit(0);
			}
	}

	public void paint(Graphics g)
	{
		g.drawImage(logoImage, 0, 0, null);
	}

}
