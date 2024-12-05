import { getDataset } from "@/utils/hf";

const Homepage: React.FC = async () => {
  const dataset = await getDataset();
  return (
    <>
      <h1>Home</h1>
      <p>{dataset}</p>
    </>
  );
};

export default Homepage;
